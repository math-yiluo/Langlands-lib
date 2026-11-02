import Langlands.Cohomology.LeftExactHomology
import Langlands.AlgebraicGeometry.Modules.CohomologyBaseChange
import Langlands.AlgebraicGeometry.Modules.HigherDirectImageOpenRestriction

/-!
# Base change of right derived functors along exact functors

Let `F₁ : C₁ ⥤ D₁` and `F₂ : C₂ ⥤ D₂` be additive functors of abelian categories, where `C₁` and
`C₂` have injective resolutions, and let `α : C₁ ⥤ C₂` and `β : D₁ ⥤ D₂` be additive functors that
preserve finite limits and homology. A natural transformation `τ : F₁ ⋙ β ⟶ α ⋙ F₂` induces, in
every degree `n`, a natural transformation

`baseChangeNatTrans τ n : F₁.rightDerived n ⋙ β ⟶ α ⋙ F₂.rightDerived n`,

the composite of
* the inverse of `LeftExactHomology.derivedNatTrans β F₁ n : (F₁ ⋙ β).rightDerived n ⟶
  F₁.rightDerived n ⋙ β`, which is invertible since `β` preserves homology;
* `NatTrans.rightDerived τ n : (F₁ ⋙ β).rightDerived n ⟶ (α ⋙ F₂).rightDerived n`;
* `compComparisonNatTrans α F₂ n : (α ⋙ F₂).rightDerived n ⟶ α ⋙ F₂.rightDerived n`, whose
  components are the comparisons `AcyclicResolution.compComparison` for the identity of
  `α ⋙ F₂`; they are defined since the positive right derived functors of the exact functor `α`
  vanish.

The components are given by `compComparisonNatTrans_app` and `baseChangeNatTrans_app`.
-/

noncomputable section

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Cohomology.ExactBaseChange

open AcyclicResolution Langlands.AlgebraicGeometry.Modules

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasInjectiveResolutions C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasInjectiveResolutions C₂]
  {D₁ : Type u₃} [Category.{v₃} D₁] [Abelian D₁]
  {D₂ : Type u₄} [Category.{v₄} D₂] [Abelian D₂]

section CompComparison

variable (α : C₁ ⥤ C₂) [α.Additive] [PreservesFiniteLimits α] [α.PreservesHomology]
  (F₂ : C₂ ⥤ D₂) [F₂.Additive]

/-- The comparison `Rⁿ(α ⋙ F₂) ⟶ α ⋙ Rⁿ F₂` for an exact functor `α`: its component at `A` is
`compComparison F₂ (Iso.refl (α ⋙ F₂)) A hA n`, where `hA` is the vanishing of the positive right
derived functors of `α` at `A`. It is natural by `compComparison_naturality`. -/
def compComparisonNatTrans (n : ℕ) : (α ⋙ F₂).rightDerived n ⟶ α ⋙ F₂.rightDerived n where
  app A := compComparison F₂ (Iso.refl (α ⋙ F₂)) A
    (fun q => DerivedSections.isZero_rightDerived_succ_of_preservesHomology α A q) n
  naturality _ _ u := compComparison_naturality F₂ (Iso.refl (α ⋙ F₂)) u _ _ n

/-- The component of `compComparisonNatTrans α F₂ n` at `A` is the comparison
`compComparison F₂ (Iso.refl (α ⋙ F₂)) A hA n`. -/
lemma compComparisonNatTrans_app (n : ℕ) (A : C₁) :
    (compComparisonNatTrans α F₂ n).app A = compComparison F₂ (Iso.refl (α ⋙ F₂)) A
      (fun q => DerivedSections.isZero_rightDerived_succ_of_preservesHomology α A q) n :=
  rfl

end CompComparison

section BaseChange

variable {F₁ : C₁ ⥤ D₁} [F₁.Additive] {F₂ : C₂ ⥤ D₂} [F₂.Additive]
  {α : C₁ ⥤ C₂} [α.Additive] [PreservesFiniteLimits α] [α.PreservesHomology]
  {β : D₁ ⥤ D₂} [β.Additive] [PreservesFiniteLimits β] [β.PreservesHomology]
  (τ : F₁ ⋙ β ⟶ α ⋙ F₂)

/-- The base change transformation `Rⁿ F₁ ⋙ β ⟶ α ⋙ Rⁿ F₂` induced by `τ : F₁ ⋙ β ⟶ α ⋙ F₂`:
the inverse of `LeftExactHomology.derivedNatTrans β F₁ n`, followed by
`NatTrans.rightDerived τ n` and `compComparisonNatTrans α F₂ n`. -/
def baseChangeNatTrans (n : ℕ) : F₁.rightDerived n ⋙ β ⟶ α ⋙ F₂.rightDerived n :=
  inv (LeftExactHomology.derivedNatTrans β F₁ n) ≫ NatTrans.rightDerived τ n ≫
    compComparisonNatTrans α F₂ n

/-- The component of `baseChangeNatTrans τ n` at `A`: the inverse of the component of
`LeftExactHomology.derivedNatTrans β F₁ n`, followed by the component of
`NatTrans.rightDerived τ n` and the comparison `compComparison F₂ (Iso.refl (α ⋙ F₂)) A hA n`. -/
lemma baseChangeNatTrans_app (n : ℕ) (A : C₁) :
    (baseChangeNatTrans τ n).app A =
      inv ((LeftExactHomology.derivedNatTrans β F₁ n).app A) ≫
        (NatTrans.rightDerived τ n).app A ≫
          compComparison F₂ (Iso.refl (α ⋙ F₂)) A
            (fun q => DerivedSections.isZero_rightDerived_succ_of_preservesHomology α A q) n := by
  rw [baseChangeNatTrans, NatTrans.comp_app, NatTrans.comp_app, NatIso.isIso_inv_app]
  rfl

end BaseChange

end Langlands.Cohomology.ExactBaseChange
