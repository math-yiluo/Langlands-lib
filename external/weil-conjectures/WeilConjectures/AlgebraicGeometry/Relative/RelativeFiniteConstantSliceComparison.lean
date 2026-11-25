/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Relative.RelativeFiniteCoefficientTransport
public import WeilConjectures.CategoryTheory.LocallyConstantFiniteTypeModules
public import WeilConjectures.CategoryTheory.ConstantCoefficientScalarExtension
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRings
public import WeilConjectures.Algebra.Homology.Strict.StrictPerfectCoefficientPackageSupplement
public import Mathlib.RingTheory.Finiteness.Defs
public import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.AlgebraicGeometry.Relative.RelativeFiniteModelSliceEquivalence
import WeilConjectures.AlgebraicGeometry.Relative.RelativeFiniteConstantModelIdentification

/-! # Constant module comparisons on each slice of the equivalent small site

## References

* Stacks Project, Modules on Sites, Tags 03CY and 093U
* Sites, Tag 03A0
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- The explicit small-site coefficient transport identifies constant local models
on each slice, keeping the same coefficient module. No finiteness assumption is needed. -/
theorem relativeFiniteConstantSliceComparison {X Y : Scheme.{u}} (g : Y ⟶ X)
    (B : Type (u + 1)) [CommRing B]
    (F : pbcModules Y ((adicTowerInverseImage g).obj (adicLisseConstantRing X B)))
    (M : ModuleCat.{u + 1} B) (V : proEtaleSiteModel Y) :
    Nonempty (F.over (AsSmall.down.obj V) ≅
      ((proEtaleModuleInverseImage g (adicLisseConstantRing X B)).obj
        ((adicLisseConstantModules X B).obj M)).over (AsSmall.down.obj V)) ↔
    Nonempty (((relativeFiniteModelModules g B).obj F).over V ≅
      ((SheafOfModules.constantCoefficientModule
        (proEtaleModelTopology Y) B).obj M).over V) := by
  let G := (proEtaleModuleInverseImage g (adicLisseConstantRing X B)).obj
    ((adicLisseConstantModules X B).obj M)
  have hslice := relativeFiniteModelSliceEquivalence g B F G V
  have hconst := relativeFiniteConstantModelIdentification g B M V
  constructor
  · intro h
    obtain ⟨e⟩ := h
    obtain ⟨e'⟩ := hslice.mp ⟨e⟩
    obtain ⟨c⟩ := hconst
    exact ⟨e' ≪≫ c⟩
  · intro h
    obtain ⟨e⟩ := h
    obtain ⟨c⟩ := hconst
    apply hslice.mpr
    exact ⟨e ≪≫ c.symm⟩

end AlgebraicGeometry.Scheme
