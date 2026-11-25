/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpShriekTransition.ShriekNormalizedTransitionData

set_option linter.privateModule false

/-! # Cocycle of normalized scalar transitions -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpShriekTransition
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
attribute [local irreducible] scalarCoordinates quotientMap
  Functor.mapDerivedCategory Functor.rightDerivedFunctor HasDerivedCategory.standard
  Padic Padic.coefficientExtensionIntegers scalarExtensionFunctor SemilinearSections.reduction
attribute [local implicit_reducible] SemilinearSections.hasDerived
  SemilinearSections.moduleAbelian
attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem transport_cocycle
    {A B C : Type*} [categoryA : Category A] [categoryB : Category B]
    [categoryC : Category C]
    {S S' : A ⥤ B} {T T' : B ⥤ C} {R R' : A ⥤ C}
    (s : S ≅ S') (t : T ≅ T') (r : R ≅ R') (a : S ⋙ T ≅ R)
    {K : A} {L : B} {M : C} (f : S.obj K ⟶ L) (g : T.obj L ⟶ M)
    (h : R.obj K ⟶ M) (w : T.map f ≫ g = a.hom.app K ≫ h) :
    T'.map (coordinateReduction s f) ≫ coordinateReduction t g =
      (coordinateAssociator s t r a).hom.app K ≫ coordinateReduction r h := by
  simp only [coordinateReduction, coordinateAssociator,
    Functor.map_comp, Category.assoc, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Iso.symm_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app]
  rw [t.inv.naturality_assoc, w]
  simp only [Iso.hom_inv_id_app_assoc]

private abbrev nativeHom {A : Type*} [categoryA : Category A] (X Y : A) :=
  @Quiver.Hom A (@ReflQuiver.toQuiver A (@catToReflQuiver A categoryA)) X Y

end AlgebraicGeometry.ProEtale.SpShriekTransition
