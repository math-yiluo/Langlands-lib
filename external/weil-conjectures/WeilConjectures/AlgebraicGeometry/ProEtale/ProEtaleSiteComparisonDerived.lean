/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Refinement.RefinementCoefficientRealization
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf

import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonFiniteLevel
import
  WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunctionAcyclic

set_option autoImplicit false

/-!
# Bounded below finite-coefficient site comparison

## References

* Stacks Project, Tag 099V, final paragraph
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

variable (T : Scheme.{u}) (Λ : Type (u + 1)) [Ring Λ] [Finite Λ]
  [TopologicalSpace Λ] [DiscreteTopology Λ]

/-- Direct image in the specified coefficient encoding: undo canonical coefficient
realization and restrict along the inclusion of the etale site. -/
noncomputable def finiteCoefficientDirectImage :
    FiniteCoefficientModules T Λ ⥤ Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  (finiteCoefficientRealization T Λ).inv ⋙ comparisonLowerStar (ModuleCat.{u + 1} Λ) T

/-- The module adjunction transported through canonical coefficient realization. -/
noncomputable def finiteCoefficientComparisonAdjunction :
    finiteCoefficientComparison T Λ ⊣ finiteCoefficientDirectImage T Λ :=
  (T.proEtaleSiteComparisonModules Λ).comp
    (finiteCoefficientRealization T Λ).asEquivalence.toAdjunction

/-- Transport enough injectives along the canonical coefficient equivalence. -/
noncomputable instance finiteCoefficientModulesEnoughInjectives :
    EnoughInjectives (FiniteCoefficientModules T Λ) :=
  EnoughInjectives.of_equivalence (finiteCoefficientRealization T Λ).inv

/-- Additivity of direct image, inherited from the specified module adjunction. -/
noncomputable instance finiteCoefficientDirectImageAdditive :
    (finiteCoefficientDirectImage T Λ).Additive :=
  (finiteCoefficientComparisonAdjunction T Λ).right_adjoint_additive

/-- The canonical adjunction on bounded below derived categories. Its left adjoint is
termwise exact inverse image; its right adjoint is the right derived direct image. -/
noncomputable def finiteCoefficientDerivedComparisonAdjunction :
    (finiteCoefficientComparison T Λ).mapDerivedCategoryPlus ⊣
      (finiteCoefficientDirectImage T Λ).rightDerivedFunctorPlus :=
  (finiteCoefficientComparisonAdjunction T Λ).derivedPlus

/-- Finite-coefficient comparison is fully faithful on all bounded below complexes,
and its canonical derived unit is a natural isomorphism. -/
theorem siteComparison_boundedBelow (T : Scheme.{u}) (Λ : Type (u + 1))
    [Ring Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] :
    Nonempty (finiteCoefficientComparison T Λ).mapDerivedCategoryPlus.FullyFaithful ∧
      IsIso (finiteCoefficientDerivedComparisonAdjunction T Λ).unit := by
  let L := comparisonUpperStar (ModuleCat.{u + 1} Λ) T
  let E := finiteCoefficientRealization T Λ
  let adj := comparisonAdjunction (ModuleCat.{u + 1} Λ) T
  obtain ⟨_, _, hunit, hacyclic⟩ := siteComparison_finiteLevel T Λ
  have hu : IsIso adj.derivedPlus.unit := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro K
    exact adj.isIso_derivedPlus_unit_app_of_rightAcyclic
      (fun I _ ↦ hunit I)
      (fun I _ n ↦ hacyclic I inferInstance (n + 1) (Nat.succ_pos n)) K
  let fL := adj.derivedPlus.fullyFaithfulLOfIsIsoUnit
  let fE := (Functor.FullyFaithful.ofFullyFaithful
    (DerivedCategory.Plus.ι ⋙ E.mapDerivedCategory)).ofIso
      E.mapDerivedCategoryPlusCompatibility.symm
  let e := Functor.mapDerivedCategoryPlusCompIso L E
  let ff := fL.comp (Functor.FullyFaithful.ofCompFaithful fE)
  let f := ff.ofIso e.symm
  have : (finiteCoefficientComparison T Λ).mapDerivedCategoryPlus.Full := f.full
  have : (finiteCoefficientComparison T Λ).mapDerivedCategoryPlus.Faithful := f.faithful
  exact ⟨⟨f⟩, inferInstance⟩

end AlgebraicGeometry.ProEtale
