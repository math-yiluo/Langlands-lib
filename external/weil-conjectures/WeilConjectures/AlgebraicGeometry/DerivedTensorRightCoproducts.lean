/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.AlgebraicGeometry.DerivedTensorSymmetry

/-! # Coproduct preservation by the shared derived tensor

Source: Stacks Project, Duality for Schemes, Tag 0A9U, first two sentences of proof;
Cohomology, Tags 06YH and 0FPB; Injectives, Tag 07D9.
(blueprint: lem-sc-derived-tensor-right-coproducts).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in

/-- Derive the homotopy tensor-Hom adjunction using K-flat and K-injective
resolutions. Unlike the bundled upstream closed instance, this argument needs
Grothendieck abelianness only in the scheme universe.
Source: the argument of `DerivedCategory.tensorHomAdjunctionQhObj` in
WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Closed; Stacks, Tag 06YH. -/
private theorem derivedTensorLeft_isLeftAdjoint (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (E : schemeDerivedCategory X) : (tensorLeft E).IsLeftAdjoint := by
  let C := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  let := SheafOfModules.monoidalCategory X.sheaf
  let := SheafOfModules.symmetricCategory X.sheaf
  have : MonoidalPreadditive C :=
    Classical.choice (SheafOfModules.tensorClosed X.sheaf).1
  let : MonoidalClosed C :=
    Classical.choice (SheafOfModules.tensorClosed X.sheaf).2.1
  have : IsGrothendieckAbelian.{u} C :=
    SheafOfModules.isGrothendieckAbelian (moduleRings X.toRingedSpace)
  have : HasColimitsOfSize.{0, 0} C := hasColimitsOfSizeShrink.{0, 0, u, u} C
  have := schemeModule_hasFunctorialFlatResolution X
  have := DerivedCategory.hasDerivedMonoidalCategory C
  have (M : C) : PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj M) :=
    preservesColimitsOfShape_of_natIso (F := tensorLeft M)
      (NatIso.ofComponents (fun N ↦ β_ M N) (by intros; simp [curriedTensor]))
  have (M N : GradedObject ℤ C) : M.HasTensor N := inferInstance
  have (M N P R : GradedObject ℤ C) :
      GradedObject.HasTensor₄ObjExt M N P R := inferInstance
  have (M N P : GradedObject ℤ C) :
      GradedObject.HasGoodTensor₁₂Tensor M N P := inferInstance
  have (M N P : GradedObject ℤ C) :
      GradedObject.HasGoodTensorTensor₂₃ M N P := inferInstance
  have (M : C) : PreservesColimitsOfShape ℤ ((curriedTensor C).obj M) :=
    inferInstance
  have : HasExactColimitsOfShape ℤ C := inferInstance
  have (j : ℤ) : HasColimitsOfShape
      (Discrete ((ComplexShape.up ℤ).π (.up ℤ) (.up ℤ) ⁻¹' {j})) C := inferInstance
  have : (HomotopyCategory.quasiIso C (.up ℤ)).localizerMorphismKFlat
      |>.IsLeftDerivabilityStructure := inferInstance
  let Q := DerivedCategory.Qh (C := C)
  let W := HomotopyCategory.quasiIso C (.up ℤ)
  let P := Q.objPreimage E
  let H := HomotopyCategory.internalHom P ⋙ Q
  let R := H.totalRightDerived Q W
  let η := H.totalRightDerivedUnit Q W
  let ε := DerivedCategory.tensorLeftQhObjCounit P
  have : R.IsRightDerivedFunctor η W := by
    dsimp [R, η]
    infer_instance
  have : (tensorLeft (Q.obj P) ⋙ R).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight ε R) W :=
    W.localizerMorphismKFlat.isLeftDerivedFunctor_comp_of_isLeftDerivabilityStructure
      ε (fun Z ↦ DerivedCategory.isIso_tensorLeftQhObjCounit_app P Z.1 Z.2) R
  have : (R ⋙ tensorLeft (Q.obj P)).IsRightDerivedFunctor
      (Functor.whiskerRight η (tensorLeft (Q.obj P)) ≫
        (Functor.associator _ _ _).hom) W :=
    (HomotopyCategory.KInjectives.localizerMorphism C)
      |>.isRightDerivedFunctor_comp_of_isRightDerivabilityStructure
        η (fun I ↦ (HomotopyCategory.KInjectives.localizerMorphism_derives H)
          |>.isIso_of_isRightDerivedFunctor η I) (tensorLeft (Q.obj P))
  let adj := (HomotopyCategory.tensorHomAdjunction P).derived W W ε η
  exact (adj.ofNatIsoLeft ((tensoringLeft _).mapIso (Q.objObjPreimageIso E))).isLeftAdjoint

/-- Tensoring on the right by any derived object preserves scheme-universe coproducts.
The localization universe w is independent of the scheme universe u.
Source: Stacks Project, Tag 0A9U, first two sentences of proof;
Cohomology, Tags 06YH and 0FPB; Injectives, Tag 07D9.
(blueprint: lem-sc-derived-tensor-right-coproducts).

Proof. Choose a K-flat representative P of E. The shared K-flat tensor comparison
identifies tensoring with E with total tensoring by P on representatives. Module
sheaf tensor preserves coproducts because it is a left adjoint in each variable.
Coproducts of cochain complexes are degreewise. In total degree n, tensoring a
coproduct complex by P therefore amounts to interchanging the coproduct of the
input complexes with the coproduct over pairs of degrees adding to n. The canonical
interchange isomorphisms commute with the tensor differential and assemble to a
natural isomorphism of complexes. Termwise coproducts give coproducts in the derived
category by derivedAmbientDirectSums, and the K-flat comparison is natural with
respect to their coprojections. Thus the image of each coproduct cofan under
tensorRight E is a colimit cofan. This proves preservation, including the empty
family. Represent the objects in the chosen localization universe w throughout;
no equality w = u and no Grothendieck instance in universe w is required. -/
theorem derivedTensorRight_preservesCoproducts (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (E : schemeDerivedCategory X) (J : Type u) :
    PreservesColimitsOfShape (Discrete J) (tensorRight E) := by
  have := derivedTensorLeft_isLeftAdjoint X E
  obtain ⟨s, hs⟩ := exists_schemeDerivedTensorSymmetry X
  let e : tensorLeft E ≅ tensorRight E :=
    NatIso.ofComponents (fun K ↦ s E K) (by
      intro K L f
      change E ◁ f ≫ (s E L).hom = (s E K).hom ≫ f ▷ E
      simpa only [id_tensorHom, tensorHom_id] using hs E E K L (𝟙 E) f)
  exact preservesColimitsOfShape_of_natIso e

end AlgebraicGeometry
