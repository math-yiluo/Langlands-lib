/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.ProperBaseChange.IntegralReductionTensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralResiduePullSquare
import WeilConjectures.CategoryTheory.DerivedCategory.KFlatAcyclic
public import WeilConjectures.AlgebraicGeometry.IntegralResidueTensorPresentation

/-! # The canonical restricted residue tensor presentation

Source: Bhatt--Scholze, Lemma 6.5.9(3), and derived scalar extension.
(blueprint: new-integral-residue-tensor-presentation)
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory MonObj Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C] [BraidedCategory C]
  [Abelian.HasFunctorialFlatResolution C]







noncomputable section NormalizationAPI

attribute [local instance] derivedTensorPresentationBraiding


end NormalizationAPI

/-- The derived monoidal structure for the fixed generic base-category data.
Source: the derived tensor construction above.
(blueprint: new-integral-residue-tensor-presentation) -/
noncomputable abbrev tensorPresentationMonoidal : MonoidalCategory (DerivedCategory C) :=
  inferInstance

end CategoryTheory

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C]
  [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
  [IsGrothendieckAbelian.{v} C] [Abelian.HasFunctorialFlatResolution C]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
  (φ : R ⟶ S) [IsMonHom φ]


end CategoryTheory.Mod

local instance instEssentiallySmallProfinite_integralResidueTensorPresentation
    : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _

namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local instance 20000] sheafBraidedCategory

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

/-- The fixed balanced tensor counit, retaining the named reduction functor.
Source: Bhatt--Scholze, Lemma 6.5.9(3), and the canonical balanced tensor counit.
(blueprint: new-integral-residue-tensor-presentation) -/
@[irreducible] noncomputable def residueExchangeTensorCounit (T : Scheme.{u}) :
    DerivedCategory.Qh ⋙ (residueExchangeReduction ℓ E T ⋙ residueExchangeRestriction ℓ E T) ⟶
      (tensorLeft ((Mod.comap (coefficientMap (integralReductionMap ℓ E) T)).obj
        (Mod.regular (condensedRingObj
          (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) T)))).mapHomotopyCategory
            (.up ℤ) ⋙ DerivedCategory.Qh := by
  unfold residueExchangeReduction integralReduction residueExchangeRestriction
  exact Mod.tensorPresentationDerivedCounit (coefficientMap (integralReductionMap ℓ E) T)

/-- The named counit presents the same left-derived tensor functor.
Source: the canonical balanced tensor left-derived property.
(blueprint: new-integral-residue-tensor-presentation) -/
theorem residueExchangeTensorCounit_isLeftDerivedFunctor (T : Scheme.{u}) :
    (residueExchangeReduction ℓ E T ⋙ residueExchangeRestriction ℓ E T).IsLeftDerivedFunctor
      (residueExchangeTensorCounit ℓ E T) (HomotopyCategory.quasiIso _ (.up ℤ)) := by
  unfold residueExchangeTensorCounit residueExchangeReduction integralReduction
    residueExchangeRestriction
  exact Mod.tensorPresentationDerivedCounit_isLeftDerivedFunctor
    (coefficientMap (integralReductionMap ℓ E) T)

/-- The canonical tensor presentation, using the fixed named functor and counit.
Source: Bhatt--Scholze, Lemma 6.5.9(3), Remark 6.8.15.
(blueprint: new-integral-residue-tensor-presentation) -/
@[irreducible] noncomputable def residueExchangeTensorIso (T : Scheme.{u}) :
    letI : MonoidalCategory (residueExchangeDerived (integralCoeff ℓ E) T) :=
      CategoryTheory.tensorPresentationMonoidal
    residueExchangeReduction ℓ E T ⋙ residueExchangeRestriction ℓ E T ≅
      tensorRight (residueExchangeCoefficient ℓ E T) := by
  letI : MonoidalCategory (residueExchangeDerived (integralCoeff ℓ E) T) :=
    CategoryTheory.tensorPresentationMonoidal
  have := residueExchangeTensorCounit_isLeftDerivedFunctor ℓ E T
  exact derivedTensorPresentationIso _ _ (residueExchangeTensorCounit ℓ E T)

end AlgebraicGeometry.ProEtale.CondensedRing
