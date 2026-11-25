/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Integral.IntegralResidueTensorPresentation
public import WeilConjectures.CategoryTheory.ModuleObjects.ResidueOrdinary.IntegralResidueOrdinaryMonoidal
public import WeilConjectures.AlgebraicGeometry.IntegralResidueDerivedMonoidal
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Braided
public import WeilConjectures.AlgebraicGeometry.IntegralResidueTensorModel

/-! # A common homotopy-level model for the residue tensor square

Source: Bhatt--Scholze, Lemma 6.5.9(3), Remark 6.8.15.
(blueprint: new-integral-residue-tensor-model)
-/

@[expose] public section

noncomputable section

universe v u u₁ u₂
open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v + 1} C] [Abelian C] [IsGrothendieckAbelian.{v + 1} C]
  [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C] [BraidedCategory C]
  [Abelian.HasFunctorialFlatResolution C]
  {D : Type u₂} [Category.{v + 1} D] [Abelian D] [IsGrothendieckAbelian.{v + 1} D]
  [MonoidalCategory D] [MonoidalClosed D] [MonoidalPreadditive D] [BraidedCategory D]
  [Abelian.HasFunctorialFlatResolution D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

attribute [local instance] instBraidedCategoryDerivedCategory_sheaf

attribute [local instance] CategoryTheory.derivedTensorPresentationBraiding

/-- The existing derived monoidal structure, with its base-category data fixed.
Source: the derived tensor construction used by `tensorModelTarget` below.
(blueprint: new-integral-residue-tensor-model) -/
noncomputable abbrev tensorModelDerivedMonoidal : MonoidalCategory (DerivedCategory D) :=
  inferInstance

variable [F.IsLeftAdjoint] [F.Monoidal]

end CategoryTheory.Functor

local instance instEssentiallySmallProfinite_integralResidueTensorModel
    : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _

namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local instance 20000] sheafBraidedCategory
attribute [local irreducible] Functor.leftDerivedFunctor Functor.mapDerivedCategory

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

/-- The residue coefficient as an ordinary integral module.
Source: Bhatt--Scholze, Lemma 6.5.9(3), Remark 6.8.15; explicit tensor comparisons.
(blueprint: new-integral-residue-tensor-model) -/
noncomputable abbrev residueExchangeOrdinaryCoefficient (T : Scheme.{u}) :=
  (Mod.comap (coefficientMap (integralReductionMap ℓ E) T)).obj
    (Mod.regular (condensedRingObj
      (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) T))

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

variable (P : HomotopyCategory
  (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
    (condensedRingObj (integralCoeff ℓ E) Y)) (.up ℤ))

/-- The explicit comparison from the target of the residue square to its ordinary model.
Source: Bhatt--Scholze, Lemma 6.5.9(3), Remark 6.8.15; explicit tensor comparisons.
(blueprint: new-integral-residue-tensor-model) -/
@[irreducible]
noncomputable def residueExchangeTensorModelTarget :
    (residueExchangeUpperStar (integralCoeff ℓ E) f).obj (DerivedCategory.Qh.obj P) ⊗
        (residueExchangeUpperStar (integralCoeff ℓ E) f).obj
          (residueExchangeCoefficient ℓ E Y) ⟶
      DerivedCategory.Qh.obj
        (((f)^*⟦integralCoeff ℓ E⟧.mapHomotopyCategory (.up ℤ)).obj
            (Functor.tensorModelCoefficient (residueExchangeOrdinaryCoefficient ℓ E Y)) ⊗
          ((f)^*⟦integralCoeff ℓ E⟧.mapHomotopyCategory (.up ℤ)).obj P) := by
  exact Functor.tensorModelTargetWith (f)^*⟦integralCoeff ℓ E⟧
    (residueExchangeUpperStar (integralCoeff ℓ E) f)
    (residueExchangeUpperStarCounit (integralCoeff ℓ E) f)
    (residueExchangeOrdinaryCoefficient ℓ E Y) P

/-- The explicit common map for the two routes in the residue square.
Source: Bhatt--Scholze, Lemma 6.5.9(3), Remark 6.8.15; explicit tensor comparisons.
(blueprint: new-integral-residue-tensor-model) -/
noncomputable def residueExchangeTensorModelMap :
    (residueExchangeUpperStar (integralCoeff ℓ E) f).obj
        ((residueExchangeRestriction ℓ E Y).obj
          ((residueExchangeReduction ℓ E Y).obj (DerivedCategory.Qh.obj P))) ⟶
      DerivedCategory.Qh.obj
        (((f)^*⟦integralCoeff ℓ E⟧.mapHomotopyCategory (.up ℤ)).obj
            (Functor.tensorModelCoefficient (residueExchangeOrdinaryCoefficient ℓ E Y)) ⊗
          ((f)^*⟦integralCoeff ℓ E⟧.mapHomotopyCategory (.up ℤ)).obj P) := by
  let := residueExchangeOrdinaryPullMonoidal ℓ E f
  exact Functor.tensorModelMapWith (f)^*⟦integralCoeff ℓ E⟧
    (residueExchangeUpperStar (integralCoeff ℓ E) f)
    (residueExchangeUpperStarCounit (integralCoeff ℓ E) f)
    (residueExchangeOrdinaryCoefficient ℓ E Y)
    (residueExchangeReduction ℓ E Y ⋙ residueExchangeRestriction ℓ E Y)
    (residueExchangeTensorCounit ℓ E Y) P

end AlgebraicGeometry.ProEtale.CondensedRing
