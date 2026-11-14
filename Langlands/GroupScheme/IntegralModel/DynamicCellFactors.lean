import Langlands.GroupScheme.IntegralModel.AmbientCellFactors
import Langlands.GroupScheme.Dynamic.AffineRepresentability
import Langlands.GroupScheme.Dynamic.OppositeBaseChange
import Langlands.GroupScheme.Dynamic.OppositeCellMono
import Langlands.GroupScheme.SubgroupBaseChange

/-! # Integral prescribed dynamic factors from integral cell coordinates -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IntegralModel

variable {A K : Type u} [CommRing A] [IsDomain A] [Field K]
    [Algebra A K] [IsFractionRing A K]
    {G : GroupScheme (Spec (CommRingCat.of K))}
    (M : IntegralModel A K G)
    (χ : (Gm (Spec (CommRingCat.of A))).toGrp ⟶ M.group)

local notation "χK" =>
  (Dynamic.baseChangeCocharacter (Spec.algebraMap A K) χ ≫ M.genericIso.hom)

/-- The actual generic inclusion of any integral dynamic unipotent
representative represents the generic dynamic subgroup. -/
theorem isRepresentedBy_generic_unipotent
    {U : GroupScheme (Spec (CommRingCat.of A))} (i : U ⟶ M.group)
    (hi : (Dynamic.unipotent χ).IsRepresentedBy i) :
    (Dynamic.unipotent χK).IsRepresentedBy (M.genericHom i) := by
  have h₀ := hi.baseChange (Spec.algebraMap A K)
  rw [← Dynamic.unipotent_baseChange] at h₀
  have h₁ := h₀.comp_iso M.genericIso
  have heq : Dynamic.unipotent χK =
      (Dynamic.unipotent (Dynamic.baseChangeCocharacter (Spec.algebraMap A K) χ)).comap
        M.genericIso.inv := by
    simpa only [Iso.symm_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id] using
      Dynamic.unipotent_eq_comap_of_iso χK M.genericIso.symm
  rw [← heq] at h₁
  exact h₁

/-- The actual generic inclusion of any integral dynamic parabolic
representative represents the generic dynamic subgroup. -/
theorem isRepresentedBy_generic_parabolic
    {P : GroupScheme (Spec (CommRingCat.of A))} (p : P ⟶ M.group)
    (hp : (Dynamic.parabolic χ).IsRepresentedBy p) :
    (Dynamic.parabolic χK).IsRepresentedBy (M.genericHom p) := by
  have h₀ := hp.baseChange (Spec.algebraMap A K)
  rw [← Dynamic.parabolic_baseChange] at h₀
  have h₁ := h₀.comp_iso M.genericIso
  have heq : Dynamic.parabolic χK =
      (Dynamic.parabolic (Dynamic.baseChangeCocharacter (Spec.algebraMap A K) χ)).comap
        M.genericIso.inv := by
    simpa only [Iso.symm_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id] using
      Dynamic.parabolic_eq_comap_of_iso χK M.genericIso.symm
  rw [← heq] at h₁
  exact h₁

variable [IsAffineHom G.X.hom]

/-- Integral opposite-cell coordinates force the two prescribed generic
dynamic factors to be integral in the original ambient model. -/
theorem integral_dynamic_factors_of_cell_lift
    {U P : GroupScheme (Spec (CommRingCat.of A))}
    (i : U ⟶ M.group) (p : P ⟶ M.group)
    (hi : (Dynamic.unipotent (Dynamic.oppositeCocharacter χ)).IsRepresentedBy i)
    (hp : (Dynamic.parabolic χ).IsRepresentedBy p)
    (x : M.integralSections)
    (c : Over.mk (𝟙 (Spec (CommRingCat.of A))) ⟶ U.X ⊗ P.X)
    (hc : c ≫ SubgroupFunctor.cellMultiplication i p = x)
    (u v : rationalPoints G)
    (hu : u ∈ (Dynamic.unipotent (Dynamic.oppositeCocharacter χK)).carrier
      (Over.mk (𝟙 _)))
    (hv : v ∈ (Dynamic.parabolic χK).carrier (Over.mk (𝟙 _)))
    (huv : u * v = M.integralPointMap x) :
    u ∈ M.integralPoints ∧ v ∈ M.integralPoints := by
  have hiK := M.isRepresentedBy_generic_unipotent (Dynamic.oppositeCocharacter χ) i hi
  have hpK := M.isRepresentedBy_generic_parabolic χ p hp
  have hiK' : (Dynamic.unipotent (Dynamic.oppositeCocharacter χK)).IsRepresentedBy
      (M.genericHom i) := by
    simpa only [Dynamic.oppositeCocharacter, Dynamic.baseChangeCocharacter_powerHom,
      Category.assoc] using hiK
  let : Mono (SubgroupFunctor.cellMultiplication (M.genericHom i) (M.genericHom p)) :=
    Dynamic.mono_oppositeCellMul χK hiK' hpK
  apply M.ambient_integral_factors_of_cell_lift i p x c hc u v _ _ huv
  · change u ∈ (SubgroupFunctor.range (M.genericHom i)).carrier (Over.mk (𝟙 _))
    rwa [hiK'.2]
  · change v ∈ (SubgroupFunctor.range (M.genericHom p)).carrier (Over.mk (𝟙 _))
    rwa [hpK.2]

/-- Integral sections lifting both prescribed generic dynamic factors. -/
def integralDynamicFactorLift
    {U P : GroupScheme (Spec (CommRingCat.of A))}
    (i : U ⟶ M.group) (p : P ⟶ M.group)
    (hi : (Dynamic.unipotent (Dynamic.oppositeCocharacter χ)).IsRepresentedBy i)
    (hp : (Dynamic.parabolic χ).IsRepresentedBy p)
    (x : M.integralSections)
    (c : Over.mk (𝟙 (Spec (CommRingCat.of A))) ⟶ U.X ⊗ P.X)
    (hc : c ≫ SubgroupFunctor.cellMultiplication i p = x)
    (u v : rationalPoints G)
    (hu : u ∈ (Dynamic.unipotent (Dynamic.oppositeCocharacter χK)).carrier
      (Over.mk (𝟙 _)))
    (hv : v ∈ (Dynamic.parabolic χK).carrier (Over.mk (𝟙 _)))
    (huv : u * v = M.integralPointMap x) :
    {y : M.integralSections × M.integralSections //
      M.integralPointMap y.1 = u ∧ M.integralPointMap y.2 = v} := by
  have h := M.integral_dynamic_factors_of_cell_lift χ i p hi hp x c hc u v hu hv huv
  exact ⟨(Classical.choose h.1, Classical.choose h.2),
    Classical.choose_spec h.1, Classical.choose_spec h.2⟩

end Langlands.GroupScheme.IntegralModel
