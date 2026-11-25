/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Point.PointFgCompleteComplexes
public import WeilConjectures.CategoryTheory.DerivedCategory.Point.PointFdComplexes
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.RingHom.Flat
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-! # Flat scalar extension and bounded finite cohomology
Source: Stacks Project, Tags 00HD and 00HT.
(blueprint: lem-weil-point-flat-scalar-extension-finite-cohomology). -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
universe u
open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

/-- An exact scalar extension to a field preserves finite cohomological support and
turns finite modules into finite-dimensional vector spaces.
Source: Stacks Project, Tag 00HD, exactness of flat tensor products;
(blueprint: lem-weil-point-flat-scalar-extension-finite-cohomology).
Proof: exactness identifies the cohomology of the tensor complex with tensor products
of the cohomology modules. An exact additive functor preserves zero objects, so the
same finite support works. Tensor products of finitely generated modules are finitely
generated over the target field, which is finite dimensionality. -/
theorem pointFiniteDimensional_of_flat_scalar_extension
    {R S : Type u} [CommRing R] [Field S] (f : R →+* S) (hf : f.Flat)
    (C : CochainComplex (ModuleCat.{u} R) ℤ)
    (hs : ∃ s : Finset ℤ, ∀ i : ℤ, i ∉ s →
      IsZero ((homologyFunctor (ModuleCat.{u} R) i).obj (Q.obj C)))
    (hfinite : ∀ i : ℤ,
      Module.Finite R ((homologyFunctor (ModuleCat.{u} R) i).obj (Q.obj C))) :
    pointFiniteDimensional S
      (Q.obj (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).obj C)) := by
  let F := ModuleCat.extendScalars.{u, u, u} f
  letI : F.Additive := (ModuleCat.extendRestrictScalarsAdj f).left_adjoint_additive
  letI : PreservesFiniteLimits F := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  letI : PreservesFiniteColimits F := inferInstance
  let iso (i : ℤ) :
      (homologyFunctor (ModuleCat.{u} S) i).obj
          (Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj C)) ≅
        F.obj ((homologyFunctor (ModuleCat.{u} R) i).obj (Q.obj C)) :=
    (homologyFunctorFactors _ i).app _ ≪≫
      (C.sc i).mapHomologyIso F ≪≫ F.mapIso ((homologyFunctorFactors _ i).app C).symm
  constructor
  · obtain ⟨s, hs⟩ := hs
    exact ⟨s, fun i hi ↦ IsZero.of_iso (F.map_isZero (hs i hi)) (iso i)⟩
  · intro i
    let M := (homologyFunctor (ModuleCat.{u} R) i).obj (Q.obj C)
    letI : Module.Finite R M := hfinite i
    have h : Module.Finite S (F.obj M) := by
      letI : Algebra R S := f.toAlgebra
      change Module.Finite S (TensorProduct R S M)
      infer_instance
    exact @Module.Finite.equiv S _ _ _ _ _ _ _ h (iso i).toLinearEquiv.symm

end DerivedCategory
