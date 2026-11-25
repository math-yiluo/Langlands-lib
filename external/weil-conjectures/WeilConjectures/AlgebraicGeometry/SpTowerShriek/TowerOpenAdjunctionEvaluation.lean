/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerShriekData
import all WeilConjectures.CategoryTheory.Exact.ExactLocalizationInverseMate
import all WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SemilinearEvaluationDerivedAdjunction

/-! # Evaluation of the tower open adjunction unit

Source: blueprint latest, integral direct-image proof, paragraph (3), and the
ordinary open-unit evaluation and termwise localization in SpTowerShriek.Open.
(blueprint: lem-sp-tower-open-adjunction-unit-evaluation)
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option linter.privateModule false
set_option synthInstance.maxSize 4096

attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor HasDerivedCategory.standard

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.SpTowerShriek

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

section ExactUnits

variable {A B₀ : Type*} [Category A] [Category B₀] [Abelian A] [Abelian B₀]
  [HasDerivedCategory A] [HasDerivedCategory B₀]
  {L : A ⥤ B₀} {R₀ : B₀ ⥤ A} [L.Additive] [R₀.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits R₀] [PreservesFiniteColimits R₀]

private def localize {F G : A ⥤ B₀} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (a : F ⟶ G) :
    F.mapDerivedCategory ⟶ G.mapDerivedCategory :=
  Localization.liftNatTrans DerivedCategory.Q (HomologicalComplex.quasiIso A (.up ℤ))
    (F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    F.mapDerivedCategory G.mapDerivedCategory
    (Functor.whiskerRight (NatTrans.mapHomologicalComplex a (.up ℤ)) DerivedCategory.Q)

private theorem localize_fac {F G : A ⥤ B₀} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (a : F ⟶ G) (K : CochainComplex A ℤ) :
    (localize a).app (DerivedCategory.Q.obj K) ≫ G.mapDerivedCategoryFactors.hom.app K =
      F.mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex a (.up ℤ)).app K) := by
  simp only [localize, Localization.liftNatTrans_app, Localization.Lifting.iso,
    Functor.whiskerRight_app, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

end ExactUnits

section Evaluation

variable {A B₀ A' B' : Type*}
  [Category A] [Category B₀] [Category A'] [Category B']
  [Abelian A] [Abelian B₀] [Abelian A'] [Abelian B']
  [HasDerivedCategory A] [HasDerivedCategory B₀]
  [HasDerivedCategory A'] [HasDerivedCategory B']
  {L : A ⥤ B₀} {R₀ : B₀ ⥤ A} {L' : A' ⥤ B'} {R' : B' ⥤ A'}
  {E₀ : A ⥤ A'} {E₁ : B₀ ⥤ B'}
  [L.Additive] [R₀.Additive] [L'.Additive] [R'.Additive]
  [E₀.Additive] [E₁.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits R₀] [PreservesFiniteColimits R₀]
  [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
  [PreservesFiniteLimits R'] [PreservesFiniteColimits R']
  [PreservesFiniteLimits E₀] [PreservesFiniteColimits E₀]
  [PreservesFiniteLimits E₁] [PreservesFiniteColimits E₁]

end Evaluation

end AlgebraicGeometry.ProEtale.SpTowerShriek
