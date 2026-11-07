import Langlands.GroupScheme.Rational.HighestWeightRankOneCoefficient
import Langlands.GroupScheme.Rational.RepresentationNormalizerWeights
import Langlands.GroupScheme.Reductive.SplitRootRankOneRelations

/-! # Actual root-string endpoints and rational Weyl images -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix Classical

namespace Langlands.GroupScheme.SplitPinning

open MatrixRepresentation
open MatrixRepresentation.AdditiveDividedPowers

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (p : SplitPinning G)
    {n : Type} [Fintype n] [DecidableEq n]
    (ρ : MatrixRepresentation G n) (lam : characterLattice p.torus)

/-- The endpoint weight is the actual reflection of the highest character. -/
theorem add_corootPairing_smul_neg_root_eq_reflection
    (i : p.rootIndex) (m : ℕ)
    (hm : latticePairing p.torus lam (p.rootDatum.coroot i) = (m : ℤ)) :
    lam + m • (-p.rootDatum.root i) = p.rootDatum.reflection i lam := by
  rw [RootPairing.reflection_apply]
  change lam + m • (-p.rootDatum.root i) =
    lam - p.rootDatum.toLinearMap lam (p.rootDatum.coroot i) • p.rootDatum.root i
  rw [p.isRootDatum.1, hm, natCast_zsmul, smul_neg, sub_eq_add_neg]

/-- The actual degree-`m` lowering coefficient restricted to the endpoint
character space. This construction does not assert that the map is nonzero. -/
def rootEndpointMap (i : p.rootIndex)
    (xm : VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ G)
    (hxm : VectorGroup.IsTorusEquivariant p.inclusion xm (-p.rootDatum.root i))
    (m : ℕ) (hm : latticePairing p.torus lam (p.rootDatum.coroot i) = (m : ℤ)) :
    p.representationWeightSpace ρ lam →ₗ[k]
      p.representationWeightSpace ρ (p.rootDatum.reflection i lam) where
  toFun v := ⟨dividedPower (ρ.restrict xm) m v, by
    have h := p.dividedPower_mem_representationWeightSpace_of_equivariant hxm ρ m v.property
    rwa [p.add_corootPairing_smul_neg_root_eq_reflection lam i m hm] at h⟩
  map_add' v w := Subtype.ext ((dividedPower (ρ.restrict xm) m).map_add v w)
  map_smul' c v := Subtype.ext ((dividedPower (ρ.restrict xm) m).map_smul c v)

@[simp] theorem rootEndpointMap_apply (i : p.rootIndex)
    (xm : VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ G)
    (hxm : VectorGroup.IsTorusEquivariant p.inclusion xm (-p.rootDatum.root i))
    (m : ℕ) (hm : latticePairing p.torus lam (p.rootDatum.coroot i) = (m : ℤ))
    (v : p.representationWeightSpace ρ lam) :
    (p.rootEndpointMap ρ lam i xm hxm m hm v : n → k) =
      dividedPower (ρ.restrict xm) m v := rfl

/-- Every root reflection preserves the actual character-space dimension. -/
theorem finrank_representationWeightSpace_root_reflection (i : p.rootIndex) :
    Module.finrank k (p.representationWeightSpace ρ (p.rootDatum.reflection i lam)) =
      Module.finrank k (p.representationWeightSpace ρ lam) := by
  let := p.isSplitTorus.isAffineHom
  obtain ⟨g, σ, hg, hσ⟩ := p.isRootDatum.2.2 i
  have h := (ρ.normalizerWeightEquiv p.inclusion hg lam).finrank_eq.symm
  change Module.finrank k ((ρ.restrict p.inclusion).characterSpace
      ((rationalCharacters.equivCharacterLattice p.torus).symm (characterAut σ lam))) =
    Module.finrank k ((ρ.restrict p.inclusion).characterSpace
      ((rationalCharacters.equivCharacterLattice p.torus).symm lam)) at h
  rw [hσ] at h
  exact h

variable [Fintype p.rootIndex] (hspan : p.rootDatum.corootSpan ℤ = ⊤)
    (hρ : p.IsHighestWeight ρ lam)
    (i : p.rootIndex)
    {xp xm : VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ G}
    (hxp : VectorGroup.IsTorusEquivariant p.inclusion xp (p.rootDatum.root i))
    (hxm : VectorGroup.IsTorusEquivariant p.inclusion xm (-p.rootDatum.root i))
    (hα : 0 < p.rootDatum.toLinearMap (p.rootDatum.root i)
      (p.rootDatum.Polarization (IntegralWeylVector.rho p.rootDatum p.base hspan)))
    (m : ℕ) (hm : latticePairing p.torus lam (p.rootDatum.coroot i) = (m : ℤ))
    (hcell : ∀ Z : Over (Spec (CommRingCat.of k)),
      RootCell.RelationOver p.inclusion (p.rootDatum.coroot i) xp xm Z)

include hρ hxp hxm hα hm hcell

/-- Since `choose(m,m)=1`, the original endpoint coefficient is injective on
the highest-character space. -/
theorem rootEndpointMap_injective [Infinite k] :
    Function.Injective (p.rootEndpointMap ρ lam i xm hxm m hm) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hz
  apply Subtype.ext
  by_contra hv0
  have hn := p.highestWeight_dividedPower_ne_zero ρ lam hspan hρ
    hxp hxm hα (p.rootDatum.coroot i) m hm hcell v.property hv0 m (by simp)
  exact hn (congrArg Subtype.val hz)

/-- The nonzero lowering endpoint identifies the highest line with its
reflected line in the original representation. -/
theorem rootEndpointMap_bijective [Infinite k] :
    Function.Bijective (p.rootEndpointMap ρ lam i xm hxm m hm) := by
  have hinj := p.rootEndpointMap_injective ρ lam hspan hρ i hxp hxm hα m hm hcell
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (p.finrank_representationWeightSpace_root_reflection ρ lam i).symm).mp hinj⟩

/-- The endpoint on any nonzero highest vector is a unit multiple of its
image under any actual rational representative of this root reflection. -/
theorem highestWeight_rootEndpoint_eq_unit_smul [Infinite k]
    {g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X}
    {σ : p.torus ≅ p.torus}
    (hg : IsNormalizingPoint p.inclusion g σ)
    (hσ : characterAut σ = p.rootDatum.reflection i)
    {v : n → k} (hv : v ∈ p.representationWeightSpace ρ lam) (hv0 : v ≠ 0) :
    ∃ c : kˣ, dividedPower (ρ.restrict xm) m v =
      (c : k) • ((ρ.rationalMatrix g : Matrix n n k) *ᵥ v) := by
  let := p.isSplitTorus.isAffineHom
  have hw := ρ.rationalMatrix_mem_characterSpace p.inclusion hg lam hv
  change (ρ.rationalMatrix g : Matrix n n k) *ᵥ v ∈
    p.representationWeightSpace ρ (characterAut σ lam) at hw
  rw [hσ] at hw
  have hw0 : (ρ.rationalMatrix g : Matrix n n k) *ᵥ v ≠ 0 := by
    intro hz
    apply hv0
    apply Matrix.mulVec_injective_of_isUnit (Units.isUnit (ρ.rationalMatrix g))
    simpa only [Matrix.mulVec_zero] using hz
  have hdim : Module.finrank k
      (p.representationWeightSpace ρ (p.rootDatum.reflection i lam)) = 1 :=
    (p.finrank_representationWeightSpace_root_reflection ρ lam i).trans hρ.2.2.1
  have hline := eq_span_singleton_of_mem_of_finrank_eq_one hdim hw hw0
  have hmem := (p.rootEndpointMap ρ lam i xm hxm m hm ⟨v, hv⟩).property
  change dividedPower (ρ.restrict xm) m v ∈
    p.representationWeightSpace ρ (p.rootDatum.reflection i lam) at hmem
  rw [hline] at hmem
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  have hn := p.highestWeight_dividedPower_ne_zero ρ lam hspan hρ
    hxp hxm hα (p.rootDatum.coroot i) m hm hcell hv hv0 m (by simp)
  have hc0 : c ≠ 0 := by
    intro hz
    apply hn
    rw [← hc, hz, zero_smul]
  exact ⟨Units.mk0 c hc0, hc.symm⟩

omit hxp hxm hcell in
/-- Linked maps and the endpoint/Weyl relation exist from the supplied pinning,
without an additional root-cell hypothesis. -/
theorem exists_highestWeight_rootEndpoint [Infinite k] :
    ∃ xp xm : VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ G,
      VectorGroup.IsTorusEquivariant p.inclusion xp (p.rootDatum.root i) ∧
      VectorGroup.IsTorusEquivariant p.inclusion xm (-p.rootDatum.root i) ∧
      (∀ Z : Over (Spec (CommRingCat.of k)),
        RootCell.RelationOver p.inclusion (p.rootDatum.coroot i) xp xm Z) ∧
      ∀ (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) (σ : p.torus ≅ p.torus),
        IsNormalizingPoint p.inclusion g σ →
        characterAut σ = p.rootDatum.reflection i →
        ∀ v : n → k, v ∈ p.representationWeightSpace ρ lam → v ≠ 0 →
          ∃ c : kˣ, dividedPower (ρ.restrict xm) m v =
            (c : k) • ((ρ.rationalMatrix g : Matrix n n k) *ᵥ v) := by
  obtain ⟨xp, xm, hxp, hxm, hcell⟩ := p.hasRootRankOneRelations i
  refine ⟨xp, xm, hxp, hxm, hcell, ?_⟩
  intro g σ hg hσ v hv hv0
  exact p.highestWeight_rootEndpoint_eq_unit_smul ρ lam hspan hρ
    i hxp hxm hα m hm hcell hg hσ hv hv0

end Langlands.GroupScheme.SplitPinning
