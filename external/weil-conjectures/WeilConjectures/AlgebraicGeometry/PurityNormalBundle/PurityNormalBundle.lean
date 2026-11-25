/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ConormalGradedAlgebra.ConormalGradedAlgebra
public import WeilConjectures.AlgebraicGeometry.Regular.RegularImmersionPureCodimension
public import WeilConjectures.AlgebraicGeometry.PurityVectorBundle.PurityVectorBundleZeroSection
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import WeilConjectures.CategoryTheory.CommAlgebraSheafModule
import WeilConjectures.AlgebraicGeometry.AffineConormalSections
import WeilConjectures.RingTheory.RegularSequenceConormal
import WeilConjectures.AlgebraicGeometry.Coherent
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
import WeilConjectures.AlgebraicGeometry.Modules.GenericRank
import WeilConjectures.RingTheory.Regular.RegularSequenceGradedPolynomial
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Topology.Sheaves.Stalks
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.QuasiCoherentSymmetricAlgebraCore

/-!
# The normal cone, its augmentation section, and the regular normal bundle

The cone is the relative spectrum of the conormal algebra for the given immersion.
The regular case uses the conormal module itself, with no globally chosen frame.

## References

* Stacks Project, Divisors, Tags 0636, 0637, 063M
* Algebra, Tag 00LN
* Stacks Tags 0630, 0636
* Stacks Tags 0636, 01LX, 01QO
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

namespace AlgebraicGeometry.PurityNormalBundle

variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- The conormal algebra as an object of the quasi-coherent algebra category. -/
def algebraObject : ObjectProperty.FullSubcategory
    (fun A : Z.CommAlgebraSheaf ↦ A.toModule.IsQuasicoherent) :=
  ⟨(ConormalGradedAlgebra.presentation i).algebra,
    (ConormalGradedAlgebra.presentation i).quasicoherent⟩

/-- The normal cone as an affine scheme over `Z`, defined by relative spectrum of
`G = direct sum I^n/I^(n+1)`, with the actual conormal algebra of this immersion. -/
def over : ObjectProperty.FullSubcategory (fun Y : Over Z ↦ IsAffineHom Y.hom) :=
  ((VectorBundleZeroSection.antiEquivalence Z).inverse.obj (algebraObject i)).unop

/-- The normal cone `Spec_Z G` for the given closed immersion. -/
def normalCone : Scheme.{u} := (over i).obj.left

/-- The affine projection from the normal cone to the closed subscheme. -/
def projection : normalCone i ⟶ Z := (over i).obj.hom

/-- The degree-zero augmentation, transported along the structure map to the algebra of
the identity scheme over `Z`. Both arrows are specified algebra morphisms. -/
def augmentationToBase : (algebraObject i).obj ⟶
    ((VectorBundleZeroSection.antiEquivalence Z).functor.obj
      (op (VectorBundleZeroSection.baseObject Z))).obj :=
  ConormalGradedAlgebra.augmentation i ≫
    Under.homMk (((VectorBundleZeroSection.antiEquivalence Z).functor.obj
      (op (VectorBundleZeroSection.baseObject Z))).obj.hom) (Category.id_comp _)

/-- The canonical section induced contravariantly by projection to degree zero. -/
def zeroSection : Z ⟶ normalCone i :=
  ((VectorBundleZeroSection.antiEquivalence Z).functor.preimage
    (((VectorBundleZeroSection.antiEquivalence Z).counitIso.app (algebraObject i)).hom ≫
      ObjectProperty.homMk (augmentationToBase i))).unop.hom.left

/-- The augmentation gives a closed section even when the immersion is not regular. -/
theorem zeroSection_spec :
    zeroSection i ≫ projection i = 𝟙 Z ∧ IsClosedImmersion (zeroSection i) := by
  have hs : zeroSection i ≫ projection i = 𝟙 Z := by
    exact Over.w
      (((VectorBundleZeroSection.antiEquivalence Z).functor.preimage
        (((VectorBundleZeroSection.antiEquivalence Z).counitIso.app (algebraObject i)).hom ≫
          ObjectProperty.homMk (augmentationToBase i))).unop.hom)
  have : IsAffineHom (projection i) := (over i).property
  have : IsClosedImmersion (zeroSection i ≫ projection i) := hs ▸ inferInstance
  exact ⟨hs, IsClosedImmersion.of_comp (zeroSection i) (projection i)⟩

end AlgebraicGeometry.PurityNormalBundle
