import Langlands.GroupScheme.Rational.HighestWeightRankOneCoefficient
import Langlands.GroupScheme.Rational.RepresentationNormalizerWeights

/-! # The actual lowering string through a highest vector -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix Polynomial Classical

namespace Langlands.GroupScheme.SplitPinning

open MatrixRepresentation
open MatrixRepresentation.AdditiveDividedPowers

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (p : SplitPinning G)
    {n : Type} [Fintype n] [DecidableEq n]
    (ρ : MatrixRepresentation G n) (lam : characterLattice p.torus)

/-- Finite linear combinations of the actual lowering coefficients on the
original vector, with no quotient by an operator kernel. -/
def rootStringMap (xm : VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ G)
    (v : n → k) (d : ℕ) : (Fin d → k) →ₗ[k] (n → k) :=
  Fintype.linearCombination k (fun a : Fin d => dividedPower (ρ.restrict xm) a.val v)

variable [Fintype p.rootIndex] (hspan : p.rootDatum.corootSpan ℤ = ⊤)
    (hρ : p.IsHighestWeight ρ lam)

include hρ

/-- Weyl reflection bounds the length of the actual lowering string, using
only the supplied torus-equivariant root map and the actual highest weight. -/
theorem highestWeight_lowering_eq_zero_of_coroot_lt
    (i : p.rootIndex)
    {xm : VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ G}
    (hxm : VectorGroup.IsTorusEquivariant p.inclusion xm (-p.rootDatum.root i))
    (hα : 0 < p.rootDatum.toLinearMap (p.rootDatum.root i)
      (p.rootDatum.Polarization (IntegralWeylVector.rho p.rootDatum p.base hspan)))
    (m : ℕ) (hm : latticePairing p.torus lam (p.rootDatum.coroot i) = (m : ℤ))
    {v : n → k} (hv : v ∈ p.representationWeightSpace ρ lam)
    {a : ℕ} (ha : m < a) :
    dividedPower (ρ.restrict xm) a v = 0 := by
  let := p.isSplitTorus.isAffineHom
  let mu := lam + a • (-p.rootDatum.root i)
  have hmu : dividedPower (ρ.restrict xm) a v ∈ p.representationWeightSpace ρ mu :=
    p.dividedPower_mem_representationWeightSpace_of_equivariant hxm ρ a hv
  have href : p.rootDatum.reflection i mu =
      lam + ((a : ℤ) - (m : ℤ)) • p.rootDatum.root i := by
    calc
      p.rootDatum.reflection i mu =
          p.rootDatum.reflection i lam + a • p.rootDatum.root i := by
        simp only [mu, map_add, map_nsmul, map_neg,
          RootPairing.reflection_apply_self, neg_neg]
      _ = lam - (m : ℤ) • p.rootDatum.root i + a • p.rootDatum.root i := by
        rw [RootPairing.reflection_apply]
        change lam - p.rootDatum.toLinearMap lam (p.rootDatum.coroot i) •
          p.rootDatum.root i + a • p.rootDatum.root i = _
        rw [p.isRootDatum.1, hm]
      _ = _ := by
        rw [sub_smul, natCast_zsmul, natCast_zsmul]
        abel
  let f := p.rootDatum.toLinearMap.flip
    (p.rootDatum.Polarization (IntegralWeylVector.rho p.rootDatum p.base hspan))
  have hpos : 0 < ((a : ℤ) - (m : ℤ)) * f (p.rootDatum.root i) :=
    mul_pos (by omega) hα
  have hgt : f lam < f (p.rootDatum.reflection i mu) := by
    rw [href, map_add, map_zsmul, zsmul_eq_mul]
    simp only [Int.cast_id]
    omega
  have hbot := p.weightSpace_eq_bot_of_pairing_gt ρ lam hspan hρ hgt
  obtain ⟨g, σ, hg, hσ⟩ := p.isRootDatum.2.2 i
  have hgw := ρ.rationalMatrix_mem_characterSpace p.inclusion hg mu hmu
  change (ρ.rationalMatrix g : Matrix n n k) *ᵥ
      dividedPower (ρ.restrict xm) a v ∈
    p.representationWeightSpace ρ (characterAut σ mu) at hgw
  rw [hσ, hbot, Submodule.mem_bot] at hgw
  apply Matrix.mulVec_injective_of_isUnit (Units.isUnit (ρ.rationalMatrix g))
  simpa only [Matrix.mulVec_zero] using hgw

variable {xp xm : VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ G}
    {α : characterLattice p.torus}
    (hxp : VectorGroup.IsTorusEquivariant p.inclusion xp α)
    (hxm : VectorGroup.IsTorusEquivariant p.inclusion xm (-α))
    (hα : 0 < p.rootDatum.toLinearMap α
      (p.rootDatum.Polarization (IntegralWeylVector.rho p.rootDatum p.base hspan)))
    (nu : cocharacterLattice p.torus) (m : ℕ)
    (hm : latticePairing p.torus lam nu = (m : ℤ))
    (hcell : ∀ Z : Over (Spec (CommRingCat.of k)),
      RootCell.RelationOver p.inclusion nu xp xm Z)

include hxp hxm hα hm hcell

/-- The normalized diagonal pairings separate every retained original lowering
coefficient whenever their binomial coefficients are nonzero. -/
theorem linearIndependent_highestWeight_lowering [Infinite k]
    {v : n → k} (hv : v ∈ p.representationWeightSpace ρ lam) (hv0 : v ≠ 0)
    (d : ℕ) (hd : ∀ a : Fin d, (m.choose a.val : k) ≠ 0) :
    LinearIndependent k (fun a : Fin d => dividedPower (ρ.restrict xm) a.val v) := by
  obtain ⟨ell, _, hpair⟩ :=
    p.exists_highestWeight_rankOne_pairing ρ lam hspan hρ
      hxp hxm hα nu m hm hcell hv hv0
  rw [Fintype.linearIndependent_iff]
  intro c hc a
  have he := congrArg (fun w => ell (dividedPower (ρ.restrict xp) a.val w)) hc
  simp only [map_sum, map_smul, map_zero, smul_eq_mul, hpair] at he
  have ha : ∑ b : Fin d, c b * (if b.val = a.val then (m.choose a.val : k) else 0) =
      c a * (m.choose a.val : k) := by
    simp only [Fin.val_inj, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true]
  rw [ha] at he
  exact (mul_eq_zero.mp he).resolve_right (hd a)

/-- The map from coefficient vectors into the original representation is
injective under the same retained-binomial hypothesis. -/
theorem rootStringMap_injective [Infinite k]
    {v : n → k} (hv : v ∈ p.representationWeightSpace ρ lam) (hv0 : v ≠ 0)
    (d : ℕ) (hd : ∀ a : Fin d, (m.choose a.val : k) ≠ 0) :
    Function.Injective (rootStringMap ρ xm v d) :=
  (p.linearIndependent_highestWeight_lowering ρ lam hspan hρ
    hxp hxm hα nu m hm hcell hv hv0 d hd).fintypeLinearCombination_injective

omit hm in
/-- At a Steinberg coroot weight the original lowering string contains
exactly `q^r` independent retained vectors. -/
theorem linearIndependent_steinberg_lowering [Infinite k]
    (q : ℕ) [Fact q.Prime] [CharP k q] (r : ℕ)
    (hweight : latticePairing p.torus lam nu = (q ^ r - 1 : ℕ))
    {v : n → k} (hv : v ∈ p.representationWeightSpace ρ lam) (hv0 : v ≠ 0) :
    LinearIndependent k
      (fun a : Fin (q ^ r) => dividedPower (ρ.restrict xm) a.val v) :=
  p.linearIndependent_highestWeight_lowering ρ lam hspan hρ
    hxp hxm hα nu (q ^ r - 1) hweight hcell hv hv0 (q ^ r)
    (fun a => RankOneSteinberg.choose_steinberg_cast_ne_zero q r a.val (by omega))

omit hm in
/-- The span here is inside the original representation, and has the full
single-root Frobenius dimension at a Steinberg coroot weight. -/
theorem finrank_steinberg_lowering_span [Infinite k]
    (q : ℕ) [Fact q.Prime] [CharP k q] (r : ℕ)
    (hweight : latticePairing p.torus lam nu = (q ^ r - 1 : ℕ))
    {v : n → k} (hv : v ∈ p.representationWeightSpace ρ lam) (hv0 : v ≠ 0) :
    Module.finrank k (Submodule.span k
      (Set.range fun a : Fin (q ^ r) => dividedPower (ρ.restrict xm) a.val v)) = q ^ r := by
  simpa only [Fintype.card_fin] using
    finrank_span_eq_card (p.linearIndependent_steinberg_lowering ρ lam hspan hρ
      hxp hxm hα nu hcell q r hweight hv hv0)

end Langlands.GroupScheme.SplitPinning
