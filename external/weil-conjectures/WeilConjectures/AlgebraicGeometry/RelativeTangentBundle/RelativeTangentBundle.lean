/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import WeilConjectures.AlgebraicGeometry.SymmetricAlgebraSheaf.SymmetricAlgebraSheafConstruction
public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.QuasiCoherentSymmetricAlgebraAffine
public import WeilConjectures.AlgebraicGeometry.VectorBundleZeroSection.VectorBundleZeroSection
public import WeilConjectures.AlgebraicGeometry.TraceFormula.DthFittingSmoothLocus

/-! # The relative tangent bundle of a smooth morphism

The total space is relative Spec of the constructed symmetric algebra of the relative
Kähler differentials. We reuse the general structure-algebra anti-equivalence and
augmentation from VectorBundleZeroSection, without its constant-rank bundle wrappers.
No Noetherian hypothesis or global choice of relative dimension is required.

## References

* Stacks Project, Constructions, Tags 01M2, 01LW and 01LX
* Stacks Tags 01UM, 01CL and 01M2
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.RelativeTangentBundle

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f]

/-- The symmetric algebra of Ω_{X/Y}, equipped with its quasi-coherence. -/
def algebraObject : ObjectProperty.FullSubcategory
    (fun A : X.CommAlgebraSheaf ↦ A.toModule.IsQuasicoherent) :=
  ⟨SymmetricAlgebraSheaf.algebra f.relativeDifferentials,
    (quasiCoherentSymmetricAlgebra_affine_comparison X f.relativeDifferentials).1⟩

/-- Relative Spec_X Sym(Ω_{X/Y}) as an affine scheme over X. -/
def over : ObjectProperty.FullSubcategory (fun Z : Over X ↦ IsAffineHom Z.hom) :=
  ((VectorBundleZeroSection.antiEquivalence X).inverse.obj (algebraObject f)).unop

/-- The relative tangent bundle T_{X/Y} = Spec_X Sym(Ω_{X/Y}). -/
def scheme : Scheme.{u} := (over f).obj.left

/-- The structural projection π: T_{X/Y} → X. -/
def projection : scheme f ⟶ X := (over f).obj.hom

/-- The unique algebra map Sym(Ω_{X/Y}) → O_X killing the degree-one generators.
This is the existing symmetric-algebra augmentation, specialized to relative differentials. -/
def augmentation : SymmetricAlgebraSheaf.algebra f.relativeDifferentials ⟶
    Under.mk (𝟙 X.sheaf) :=
  VectorBundleZeroSection.augmentation X f.relativeDifferentials

/-- The augmentation's fully faithful inverse image, with source the identity X-scheme.
The counit identifies the structure algebra of the relative spectrum with Sym(Ω_{X/Y}). -/
def zeroSectionOver : VectorBundleZeroSection.baseObject X ⟶ over f :=
  ((VectorBundleZeroSection.antiEquivalence X).functor.preimage
    (((VectorBundleZeroSection.antiEquivalence X).counitIso.app (algebraObject f)).hom ≫
      ObjectProperty.homMk
        (VectorBundleZeroSection.augmentationToBase X f.relativeDifferentials))).unop

/-- The zero section z: X → T_{X/Y}, contravariantly induced by the augmentation. -/
def zeroSection : X ⟶ scheme f := (zeroSectionOver f).hom.left

/-- The symmetric algebra identified with the direct-image structure algebra of π. -/
def algebraIso : SymmetricAlgebraSheaf.algebra f.relativeDifferentials ≅
    Under.mk (⟨(projection f).c⟩ : X.sheaf ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} (projection f).base).obj (scheme f).sheaf) :=
  ((ObjectProperty.ι (fun A : X.CommAlgebraSheaf ↦ A.toModule.IsQuasicoherent)).mapIso
    ((VectorBundleZeroSection.antiEquivalence X).counitIso.app (algebraObject f))).symm

/-- The affine comparison with Spec Sym_{O_X(U)}(Ω_{X/Y}(U)), induced by the
sheafification unit and the relative-spectrum algebra identification. -/
def affineChart (U : X.affineOpens) :
    ((projection f) ⁻¹ᵁ U.1).toScheme ⟶
      Spec (.of (SymmetricAlgebraSheaf.sections f.relativeDifferentials (op U.1))) :=
  ((projection f) ⁻¹ᵁ U.1).toSpecΓ ≫
    Spec.map (CommRingCat.ofHom
      (((algebraIso f).hom.right.hom.app (op U.1)).hom.comp
        (SymmetricAlgebraSheaf.sectionMap f.relativeDifferentials (op U.1))))

attribute [local irreducible] VectorBundleZeroSection.antiEquivalence

end AlgebraicGeometry.RelativeTangentBundle
