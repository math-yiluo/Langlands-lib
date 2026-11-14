import Langlands.GroupScheme.IntegralModel
import Langlands.GroupScheme.Dynamic.OppositeBaseChange
import Langlands.GroupScheme.SubgroupFunctor.CellMultiplication
import Langlands.GroupScheme.SubgroupBaseChange
import Langlands.GroupScheme.Rational.RootSubgroupSeparation

/-! # Generic opposite-cell coordinates of integral sections -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj ValuativeRel

namespace Langlands.GroupScheme

section GenericCell

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom]
    (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)

/-- A torus-normalizing point in a generic opposite cell centralizes that torus. -/
theorem normalizer_mem_centralizer_of_generic_oppositeCell
    (hZ : Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i) = torusCentralizer i)
    (n : normalizerPoints i) {v p : rationalPoints G}
    (hv : v ∈ (Dynamic.unipotent
      (Dynamic.oppositeCocharacter (CommGroupScheme.groupHom ν ≫ i))).carrier _)
    (hp : p ∈ (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).carrier _)
    (hn : n.val = v * p) : n.val ∈ centralizerPoints i := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨⟨u, z⟩, ⟨hu, hz, hpz⟩, _⟩ :=
    RationalPoint.existsUnique_unipotent_mul_levi (CommGroupScheme.groupHom ν ≫ i) hp
  have hz' : z ∈ centralizerPoints i := by
    rw [← torusCentralizer_carrier_base]
    rwa [← hZ]
  let m : normalizerPoints i :=
    n * ⟨z⁻¹, (normalizerPoints i).inv_mem
      (centralizerPoints_le_normalizerPoints i hz')⟩
  have hm : m = 1 :=
    normalizer_eq_one_of_unipotent_product i ν m ⟨v, hv⟩ ⟨u, hu⟩
      (by change n.val * z⁻¹ = v * u; rw [hn, hpz]; group)
  have hnz : n.val = z := by
    have he : n.val * z⁻¹ = 1 := congrArg Subtype.val hm
    exact mul_inv_eq_one.mp he
  rwa [hnz]

end GenericCell

namespace IntegralModel

section GenericCoordinates

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    {G : GroupScheme (Spec (CommRingCat.of K))}
    (M : IntegralModel R K G)
    (χ : (Gm (Spec (CommRingCat.of R))).toGrp ⟶ M.group)
    {U P : GroupScheme (Spec (CommRingCat.of R))}
    (i : U ⟶ M.group) (p : P ⟶ M.group)
    (hi : (Dynamic.unipotent (Dynamic.oppositeCocharacter χ)).IsRepresentedBy i)
    (hp : (Dynamic.parabolic χ).IsRepresentedBy p)

include hi hp in
/-- Actual integral opposite-cell coordinates give opposite-cell factors
of the same generic point, through the model's specified generic identification. -/
theorem generic_oppositeCell_of_integral_lift (x : M.integralSections)
    (a : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ U.X ⊗ P.X)
    (ha : a ≫ SubgroupFunctor.cellMultiplication i p = x) :
    ∃ v ∈ (Dynamic.unipotent (Dynamic.oppositeCocharacter
        (Dynamic.baseChangeCocharacter (Spec.algebraMap R K) χ ≫
          M.genericIso.hom))).carrier (Over.mk (𝟙 _)),
      ∃ w ∈ (Dynamic.parabolic
        (Dynamic.baseChangeCocharacter (Spec.algebraMap R K) χ ≫
          M.genericIso.hom)).carrier (Over.mk (𝟙 _)),
        M.integralPointMap x = v * w := by
  let v := a ≫ fst U.X P.X
  let w := a ≫ snd U.X P.X
  let vK := baseChangeSectionHom (Spec.algebraMap R K) U v
  let wK := baseChangeSectionHom (Spec.algebraMap R K) P w
  have hiK := hi.baseChange (Spec.algebraMap R K)
  rw [← Dynamic.unipotent_baseChange, Dynamic.oppositeCocharacter,
    Dynamic.baseChangeCocharacter_powerHom] at hiK
  have hpK := hp.baseChange (Spec.algebraMap R K)
  rw [← Dynamic.parabolic_baseChange] at hpK
  have hvK : vK ≫ ((GroupScheme.baseChange (Spec.algebraMap R K)).map i).hom.hom ∈
      (Dynamic.unipotent (Dynamic.oppositeCocharacter
        (Dynamic.baseChangeCocharacter (Spec.algebraMap R K) χ))).carrier _ :=
    hiK.2 ▸ SubgroupFunctor.mem_range.mpr ⟨vK, rfl⟩
  have hwK : wK ≫ ((GroupScheme.baseChange (Spec.algebraMap R K)).map p).hom.hom ∈
      (Dynamic.parabolic (Dynamic.baseChangeCocharacter
        (Spec.algebraMap R K) χ)).carrier _ :=
    hpK.2 ▸ SubgroupFunctor.mem_range.mpr ⟨wK, rfl⟩
  have hv := Dynamic.unipotent_le_comap _ M.genericIso.hom _ hvK
  have hw := Dynamic.parabolic_le_comap _ M.genericIso.hom _ hwK
  have hv' : M.integralPointMap (v ≫ i.hom.hom) ∈
      (Dynamic.unipotent (Dynamic.oppositeCocharacter
        (Dynamic.baseChangeCocharacter (Spec.algebraMap R K) χ ≫
          M.genericIso.hom))).carrier _ := by
    change (baseChangeSectionHom (Spec.algebraMap R K) M.group
      (v ≫ i.hom.hom)) ≫ M.genericIso.hom.hom.hom ∈ _
    rw [baseChangeSectionHom_naturality]
    simpa only [SubgroupFunctor.mem_comap, Dynamic.oppositeCocharacter,
      Category.assoc] using hv
  have hw' : M.integralPointMap (w ≫ p.hom.hom) ∈
      (Dynamic.parabolic (Dynamic.baseChangeCocharacter
        (Spec.algebraMap R K) χ ≫ M.genericIso.hom)).carrier _ := by
    change (baseChangeSectionHom (Spec.algebraMap R K) M.group
      (w ≫ p.hom.hom)) ≫ M.genericIso.hom.hom.hom ∈ _
    rw [baseChangeSectionHom_naturality]
    exact hw
  refine ⟨_, hv', _, hw', ?_⟩
  rw [← map_mul]
  apply congrArg M.integralPointMap
  rw [← ha]
  simp only [SubgroupFunctor.cellMultiplication, MonObj.comp_mul, v, w, Category.assoc]

/-- A selected pair of actual generic factors from an integral opposite-cell
coordinate, with the subgroup memberships and product equality retained. -/
def genericOppositeCellFactorPair (x : M.integralSections)
    (a : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ U.X ⊗ P.X)
    (ha : a ≫ SubgroupFunctor.cellMultiplication i p = x) :
    {vw : rationalPoints G × rationalPoints G //
      vw.1 ∈ (Dynamic.unipotent (Dynamic.oppositeCocharacter
        (Dynamic.baseChangeCocharacter (Spec.algebraMap R K) χ ≫
          M.genericIso.hom))).carrier (Over.mk (𝟙 _)) ∧
      vw.2 ∈ (Dynamic.parabolic
        (Dynamic.baseChangeCocharacter (Spec.algebraMap R K) χ ≫
          M.genericIso.hom)).carrier (Over.mk (𝟙 _)) ∧
      M.integralPointMap x = vw.1 * vw.2} :=
  Classical.indefiniteDescription _ (by
    obtain ⟨v, hv, w, hw, he⟩ :=
      M.generic_oppositeCell_of_integral_lift χ i p hi hp x a ha
    exact ⟨(v, w), hv, hw, he⟩)

end GenericCoordinates

end IntegralModel
end Langlands.GroupScheme
