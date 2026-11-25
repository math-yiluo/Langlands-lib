/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleLevelInverseTransport
import all WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleInverseTensorCoherence
import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageExact

/-! # Quotients of finite inverse-image coefficient transport

Source: Zheng, Construction 5.15, Lemma 5.16 and Proposition 2.29(2).
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genSizeOf false
set_option genCtorIdx false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor SheafOfModules
namespace AlgebraicGeometry
attribute [local instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived

attribute [local irreducible] siteCoefficientTensorAdj coefficientQuotientSheaf
  coefficientQuotientMap CategoryTheory.constantSheaf
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true

private def insert {T : Scheme.{u}}
    {R S : Sheaf T.smallEtaleTopology CommRingCat.{u + 1}} (a : R ⟶ S)
    (M : SheafOfModules.{u + 1}
      ((sheafCompose T.smallEtaleTopology (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) :=
  (sheafCompose T.smallEtaleTopology (forget AddCommGrpCat.{u + 1})).map
    (siteTensorUnitUnderlying.{u + 1, u, u + 1} a M)

section Quotient
variable {O O' : Type (u + 1)} [CommRing O] [CommRing O'] {ell : O} {mu : O'}
    {phi : O →+* O'} {index : ℕ →o ℕ}
    {a : StrictEtaleCoefficientChange O O' ell mu phi index}
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    {SA : StrictEtaleCompactSupport O ell c} {SB : StrictEtaleCompactSupport O' mu c}
    {TX : StrictEtaleCoefficientTransport a X SA.PX SB.PX}
    {TZ : StrictEtaleCoefficientTransport a c.Z SA.PZ SB.PZ}
    (qX : StrictEtaleTransportQuotient TX) (qZ : StrictEtaleTransportQuotient TZ)
    (finite : ∀ n, StrictEtaleLevelInverseTransport TX TZ SA.openImage SB.openImage
      SA.openDerived.level SB.openDerived.level n)

section ScalarPreservation
variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (T : GrothendieckTopology C)
    [T.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
    [T.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    [HasSheafify T AddCommGrpCat.{u + 1}] [HasWeakSheafify T CommRingCat.{u + 1}]
    [HasWeakSheafify T (Type (u + 1))]
    [T.HasSheafCompose (CategoryTheory.forget CommRingCat.{u + 1})]
    [T.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{u + 1})]

end ScalarPreservation

end Quotient

private theorem inverse_three_eq {C : Type*} [Category C]
    {A B D E F G : C} (f₁ : A ≅ B) (f₂ : B ≅ D) (f₃ : D ≅ E)
    (g₁ : A ≅ F) (g₂ : F ≅ G) (g₃ : G ≅ E)
    (h : f₁.hom ≫ f₂.hom ≫ f₃.hom = g₁.hom ≫ g₂.hom ≫ g₃.hom) :
    f₃.inv ≫ f₂.inv ≫ f₁.inv = g₃.inv ≫ g₂.inv ≫ g₁.inv := by
  have he : f₁ ≪≫ f₂ ≪≫ f₃ = g₁ ≪≫ g₂ ≪≫ g₃ :=
    Iso.ext h
  simpa only [Iso.trans_inv, Category.assoc] using congrArg Iso.inv he

private theorem inverse_cube
    {A B C D E F G H I : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Category E] [Category F] [Category G] [Category H]
    (r : A ⥤ B) (s : C ⥤ D) (t : E ⥤ F) (u : G ⥤ H)
    (a : A ⥤ C) (b : B ⥤ D) (c : E ⥤ G) (d : F ⥤ H)
    (i : A ⥤ E) (j : B ⥤ F) (k : C ⥤ G) (l : D ⥤ H)
    (qZ : r ⋙ b ≅ a ⋙ s) (gB : s ⋙ l ≅ k ⋙ u)
    (fm : a ⋙ k ≅ i ⋙ c) (fn : b ⋙ l ≅ j ⋙ d)
    (gA : r ⋙ j ≅ i ⋙ t) (qX : t ⋙ d ≅ c ⋙ u)
    (Q : I → A) (good : I → Prop)
    (extQ : ∀ {F0 F1 : A ⥤ H} (α β : F0 ⟶ F1),
      (∀ P, good P → α.app (Q P) = β.app (Q P)) → α = β)
    (h : ∀ P, good P →
      l.map (qZ.hom.app (Q P)) ≫ gB.hom.app (a.obj (Q P)) ≫
          u.map (fm.hom.app (Q P)) =
        fn.hom.app (r.obj (Q P)) ≫ d.map (gA.hom.app (Q P)) ≫
          qX.hom.app (i.obj (Q P))) (M : A) :
    u.map (fm.inv.app M) ≫ gB.inv.app (a.obj M) ≫ l.map (qZ.inv.app M) =
      qX.inv.app (i.obj M) ≫ d.map (gA.inv.app M) ≫ fn.inv.app (r.obj M) := by
  let α : (r ⋙ b) ⋙ l ⟶ (i ⋙ c) ⋙ u :=
    Functor.whiskerRight qZ.hom l ≫ Functor.whiskerLeft a gB.hom ≫
      Functor.whiskerRight fm.hom u
  let β : (r ⋙ b) ⋙ l ⟶ (i ⋙ c) ⋙ u :=
    Functor.whiskerLeft r fn.hom ≫ Functor.whiskerRight gA.hom d ≫
      Functor.whiskerLeft i qX.hom
  have he := NatTrans.congr_app (extQ α β h) M
  have hi := inverse_three_eq (l.mapIso (qZ.app M)) (gB.app (a.obj M))
    (u.mapIso (fm.app M)) (fn.app (r.obj M)) (d.mapIso (gA.app M))
    (qX.app (i.obj M))
    (by simpa only [α, β, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.mapIso_hom, Iso.app_hom] using he)
  simpa only [Functor.mapIso_inv, Iso.app_inv] using hi

end AlgebraicGeometry
