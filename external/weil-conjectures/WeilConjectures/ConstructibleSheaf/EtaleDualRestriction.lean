/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits

import WeilConjectures.SixFunctors.Etale.UpperLowerStar.InternalHom
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal

/-! # Étale restriction of coefficient duals

Source: the local internal Hom argument in the docstring of
`WeilConjectures/ConstructibleSheaf/Monoidal.lean`, `IsFiniteLocallyConstantSheaf.ihom_unit`.
(blueprint: lem-weil-pbc-etale-dual-restriction)
-/

@[expose] public section

universe u
open CategoryTheory MonoidalCategory
namespace AlgebraicGeometry.Scheme

/-- Étale pullback commutes with the coefficient dual, without finiteness assumptions.

Source: `WeilConjectures/ConstructibleSheaf/Monoidal.lean`,
`IsFiniteLocallyConstantSheaf.ihom_unit`, restriction to a trivializing neighborhood.

Proof: Identify the small étale site of U with the slice of the small étale site of X
at U. The sections of the internal Hom over an object V are the module of sheaf
morphisms on the site sliced at V. Slicing first at U and then at V gives the same
site as slicing directly at V. Thus restriction preserves internal Hom, naturally
in both arguments. The restricted monoidal unit is the monoidal unit. Transport this
comparison through the equivalence between the slice site and the small étale site of U.
This argument applies to arbitrary sheaves; it does not claim the same for arbitrary
scheme pullbacks.
(blueprint: lem-weil-pbc-etale-dual-restriction) -/
theorem nonempty_etaleDualRestrictionIso
    {X : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ]
    (U : X.Etale) (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Nonempty ((Etale.upperStar (ModuleCat.{u + 1} Λ) U.hom).obj
      ((ihom F).obj (𝟙_ _)) ≅
      (ihom ((Etale.upperStar (ModuleCat.{u + 1} Λ) U.hom).obj F)).obj (𝟙_ _)) := by
  have := Etale.isIso_ihomComparison_upperStar (ModuleCat.{u + 1} Λ) U.hom F
  let e := asIso ((Functor.LaxMonoidal.ihomComparison
    (Etale.upperStar (ModuleCat.{u + 1} Λ) U.hom) F).app (𝟙_ _))
  exact ⟨e ≪≫ (ihom ((Etale.upperStar (ModuleCat.{u + 1} Λ) U.hom).obj F)).mapIso
    (Functor.Monoidal.εIso (Etale.upperStar (ModuleCat.{u + 1} Λ) U.hom)).symm⟩

end AlgebraicGeometry.Scheme
