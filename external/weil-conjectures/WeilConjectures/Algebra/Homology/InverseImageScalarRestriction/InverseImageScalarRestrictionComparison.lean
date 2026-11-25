/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-! # Inverse image and restriction of scalars

The comparison is fixed by the underlying inverse image of sheaves of sets.
Source: Stacks Project, Modules on Sites, Tags 03D2 and 03DA.
(blueprint: lem-pur-inverse-image-scalar-restriction-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe w uT vT uC vC uD vD
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
namespace SheafOfModules.InverseImageScalarRestriction

private noncomputable abbrev base
    {T : Type uT} [Category.{vT} T] [EssentiallySmall.{w} T] {τ : GrothendieckTopology T}
    [τ.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    (R : Sheaf τ CommRingCat.{w}) :=
  (sheafCompose τ (forget₂ CommRingCat.{w} RingCat.{w})).obj R

private noncomputable abbrev sets
    {T : Type uT} [Category.{vT} T] [EssentiallySmall.{w} T] {τ : GrothendieckTopology T}
    [τ.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    (R : Sheaf τ CommRingCat.{w}) :=
  SheafOfModules.toSheaf (base R) ⋙ sheafCompose τ (CategoryTheory.forget AddCommGrpCat.{w})

private noncomputable abbrev ringSets
    {T : Type uT} [Category.{vT} T] [EssentiallySmall.{w} T] {τ : GrothendieckTopology T}
    [τ.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    (R : Sheaf τ CommRingCat.{w}) := (sheafCompose τ (CategoryTheory.forget CommRingCat.{w})).obj R

private noncomputable def addMap
    {T : Type uT} [Category.{vT} T] [EssentiallySmall.{w} T] {τ : GrothendieckTopology T}
    [τ.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    {R : Sheaf τ CommRingCat.{w}} (M : SheafOfModules.{w} (base R)) :
    (sets R).obj M ⊗ (sets R).obj M ⟶ (sets R).obj M :=
  ⟨{ app := fun W ↦ ↾(fun z ↦ @Add.add (M.val.obj W) inferInstance z.1 z.2)
     naturality := by intro W V f; ext z; exact ((M.val.map f).hom.map_add _ _).symm }⟩

private noncomputable def smulMap
    {T : Type uT} [Category.{vT} T] [EssentiallySmall.{w} T] {τ : GrothendieckTopology T}
    [τ.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    {R : Sheaf τ CommRingCat.{w}} (M : SheafOfModules.{w} (base R)) :
    ringSets R ⊗ (sets R).obj M ⟶ (sets R).obj M :=
  ⟨{ app := fun W ↦ ↾(fun z ↦ @SMul.smul (R.obj.obj W) (M.val.obj W)
        inferInstance z.1 z.2)
     naturality := by intro W V f; ext z; exact (M.val.map_smul f z.1 z.2).symm }⟩

private noncomputable def pairPreimage
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
    {K : GrothendieckTopology C} {H : GrothendieckTopology D}
    (L : Sheaf K (Type w) ⥤ Sheaf H (Type w)) [PreservesFiniteLimits L]
    (X Y : Sheaf K (Type w)) (W : Dᵒᵖ)
    (x : (L.obj X).obj.obj W) (y : (L.obj Y).obj.obj W) :
    (L.obj (X ⊗ Y)).obj.obj W :=
  (inv (CartesianMonoidalCategory.prodComparison L X Y)).hom.app W (x, y)

private theorem pairPreimage_fst
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
    {K : GrothendieckTopology C} {H : GrothendieckTopology D}
    (L : Sheaf K (Type w) ⥤ Sheaf H (Type w)) [PreservesFiniteLimits L]
    (X Y : Sheaf K (Type w)) (W : Dᵒᵖ)
    (x : (L.obj X).obj.obj W) (y : (L.obj Y).obj.obj W) :
    (L.map (CartesianMonoidalCategory.fst X Y)).hom.app W
      (pairPreimage L X Y W x y) = x := by
  exact congrArg (fun f ↦ f.hom.app W (x, y))
    (CartesianMonoidalCategory.inv_prodComparison_map_fst L X Y)

private theorem pairPreimage_snd
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
    {K : GrothendieckTopology C} {H : GrothendieckTopology D}
    (L : Sheaf K (Type w) ⥤ Sheaf H (Type w)) [PreservesFiniteLimits L]
    (X Y : Sheaf K (Type w)) (W : Dᵒᵖ)
    (x : (L.obj X).obj.obj W) (y : (L.obj Y).obj.obj W) :
    (L.map (CartesianMonoidalCategory.snd X Y)).hom.app W
      (pairPreimage L X Y W x y) = y := by
  exact congrArg (fun f ↦ f.hom.app W (x, y))
    (CartesianMonoidalCategory.inv_prodComparison_map_snd L X Y)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- Compose pointwise equalities to avoid rewriting through the bundled restriction presentations.
private theorem inverse_change_hom
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
    {K : GrothendieckTopology C} {H : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [H.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    {L L' : Sheaf K (Type w) ⥤ Sheaf H (Type w)} [PreservesFiniteLimits L]
    {R S : Sheaf K CommRingCat.{w}} {RU SU : Sheaf H CommRingCat.{w}}
    (A : SheafOfModules.AlgebraicInverseImage L R RU)
    (B : SheafOfModules.AlgebraicInverseImage L' S SU)
    (a : R ⟶ S) (b : RU ⟶ SU) (h : L = L')
    (hc : A.ringUnderlying.hom ≫ (sheafCompose H (CategoryTheory.forget CommRingCat.{w})).map b =
      L.map ((sheafCompose K (CategoryTheory.forget CommRingCat.{w})).map a) ≫
        eqToHom (congrArg (fun F ↦ F.obj (ringSets S)) h) ≫ B.ringUnderlying.hom)
    (M : SheafOfModules.{w} (base S)) :
    ∃ f : A.modules.obj ((SheafOfModules.restrictScalars
        ((sheafCompose K (forget₂ CommRingCat.{w} RingCat.{w})).map a)).obj M) ⟶
        (SheafOfModules.restrictScalars
          ((sheafCompose H (forget₂ CommRingCat.{w} RingCat.{w})).map b)).obj (B.modules.obj M),
      (sets RU).map f =
        A.moduleUnderlying.hom.app _ ≫
          eqToHom (congrArg (fun F ↦ F.obj ((sets S).obj M)) h) ≫
          B.moduleUnderlying.inv.app M := by
  subst L'
  let MR := (SheafOfModules.restrictScalars
    ((sheafCompose K (forget₂ CommRingCat.{w} RingCat.{w})).map a)).obj M
  let N := A.modules.obj MR
  let N' := (SheafOfModules.restrictScalars
    ((sheafCompose H (forget₂ CommRingCat.{w} RingCat.{w})).map b)).obj (B.modules.obj M)
  let α : (sets RU).obj N ⟶ (sets RU).obj N' :=
    A.moduleUnderlying.hom.app MR ≫ B.moduleUnderlying.inv.app M
  have ha (W : Dᵒᵖ) (x y : N.val.obj W) :
      α.hom.app W (x + y) =
        (show N'.val.obj W from α.hom.app W x) +
          (show N'.val.obj W from α.hom.app W y) := by
    let X := (sets S).obj M
    let u : N.val.obj W → (L.obj X).obj.obj W :=
      (A.moduleUnderlying.hom.app MR).hom.app W
    let v : (L.obj X).obj.obj W → N.val.obj W :=
      (A.moduleUnderlying.inv.app MR).hom.app W
    let w : (L.obj X).obj.obj W → (B.modules.obj M).val.obj W :=
      (B.moduleUnderlying.inv.app M).hom.app W
    let z := pairPreimage L X X W (u x) (u y)
    have hp := pairPreimage_fst L X X W (u x) (u y)
    have hq := pairPreimage_snd L X X W (u x) (u y)
    have hv (t : N.val.obj W) : v (u t) = t :=
      congrArg (fun f ↦ f.hom.app W t) (A.moduleUnderlying.hom_inv_id_app MR)
    have hA : v ((L.map (addMap M)).hom.app W z) = x + y :=
      (A.moduleAdd MR (X ⊗ X) (CartesianMonoidalCategory.fst X X)
        (CartesianMonoidalCategory.snd X X) (addMap M) (fun _ _ ↦ rfl) W z).trans
        (congrArg₂ (fun (a b : N.val.obj W) ↦ a + b)
          ((congrArg v hp).trans (hv x)) ((congrArg v hq).trans (hv y)))
    have hB : w ((L.map (addMap M)).hom.app W z) = w (u x) + w (u y) :=
      (B.moduleAdd M (X ⊗ X) (CartesianMonoidalCategory.fst X X)
        (CartesianMonoidalCategory.snd X X) (addMap M) (fun _ _ ↦ rfl) W z).trans
        (congrArg₂ (fun (a b : (B.modules.obj M).val.obj W) ↦ a + b)
          (congrArg w hp) (congrArg w hq))
    have hu (t : (L.obj X).obj.obj W) : u (v t) = t :=
      congrArg (fun f ↦ f.hom.app W t) (A.moduleUnderlying.inv_hom_id_app MR)
    exact (congrArg (fun t ↦ w (u t)) hA).symm.trans
      ((congrArg w (hu _)).trans hB)
  have hs (W : Dᵒᵖ) (r : RU.obj.obj W) (x : N.val.obj W) :
      α.hom.app W (r • x) = r • (show N'.val.obj W from α.hom.app W x) := by
    let X := (sets S).obj M
    let Y := ringSets R
    let u : N.val.obj W → (L.obj X).obj.obj W :=
      (A.moduleUnderlying.hom.app MR).hom.app W
    let v : (L.obj X).obj.obj W → N.val.obj W :=
      (A.moduleUnderlying.inv.app MR).hom.app W
    let w : (L.obj X).obj.obj W → (B.modules.obj M).val.obj W :=
      (B.moduleUnderlying.inv.app M).hom.app W
    let z := pairPreimage L Y X W ((A.ringUnderlying.inv).hom.app W r) (u x)
    let t : Y ⊗ X ⟶ X :=
      (CartesianMonoidalCategory.lift
        (CartesianMonoidalCategory.fst Y X ≫
          (sheafCompose K (CategoryTheory.forget CommRingCat.{w})).map a)
        (CartesianMonoidalCategory.snd Y X)) ≫ smulMap M
    have hp := pairPreimage_fst L Y X W ((A.ringUnderlying.inv).hom.app W r) (u x)
    have hq := pairPreimage_snd L Y X W ((A.ringUnderlying.inv).hom.app W r) (u x)
    have hr : (A.ringUnderlying.hom).hom.app W
        ((L.map (CartesianMonoidalCategory.fst Y X)).hom.app W z) = r :=
      (congrArg ((A.ringUnderlying.hom).hom.app W) hp).trans
        (congrArg (fun f ↦ f.hom.app W r) A.ringUnderlying.inv_hom_id)
    have hx : v ((L.map (CartesianMonoidalCategory.snd Y X)).hom.app W z) = x :=
      (congrArg v hq).trans
        (congrArg (fun f ↦ f.hom.app W x) (A.moduleUnderlying.hom_inv_id_app MR))
    have hr' : (B.ringUnderlying.hom).hom.app W
      ((L.map (CartesianMonoidalCategory.fst Y X ≫
        (sheafCompose K (CategoryTheory.forget CommRingCat.{w})).map a)).hom.app W z) =
        b.hom.app W r := by
      have h := congrArg (fun f ↦ f.hom.app W
        ((L.map (CartesianMonoidalCategory.fst Y X)).hom.app W z)) hc
      simp only [eqToHom_refl, Category.id_comp] at h
      erw [L.map_comp]
      exact h.symm.trans (congrArg (fun q ↦ b.hom.app W q) hr)
    have hA : v ((L.map t).hom.app W z) = r • x :=
      (A.moduleSMul MR (Y ⊗ X) (CartesianMonoidalCategory.fst Y X)
        (CartesianMonoidalCategory.snd Y X) t (fun _ _ ↦ rfl) W z).trans
        (congrArg₂ (fun (r : RU.obj.obj W) (x : N.val.obj W) ↦ r • x) hr hx)
    have hB : w ((L.map t).hom.app W z) = b.hom.app W r • w (u x) :=
      (B.moduleSMul M (Y ⊗ X)
        (CartesianMonoidalCategory.fst Y X ≫
          (sheafCompose K (CategoryTheory.forget CommRingCat.{w})).map a)
        (CartesianMonoidalCategory.snd Y X) t (fun _ _ ↦ rfl) W z).trans
        (congrArg₂ (fun (r : SU.obj.obj W) (x : (B.modules.obj M).val.obj W) ↦ r • x)
          hr' (congrArg w hq))
    have hu (q : (L.obj X).obj.obj W) : u (v q) = q :=
      congrArg (fun f ↦ f.hom.app W q) (A.moduleUnderlying.inv_hom_id_app MR)
    exact (congrArg (fun q ↦ w (u q)) hA).symm.trans
      ((congrArg w (hu _)).trans hB)
  let f : N ⟶ N' :=
    { val :=
        { app := fun W ↦
            @ModuleCat.ofHom ((base RU).obj.obj W) inferInstance
              (N.val.obj W) (N'.val.obj W)
              (N.val.obj W).isAddCommGroup (N.val.obj W).isModule
              (N'.val.obj W).isAddCommGroup (N'.val.obj W).isModule
              { toFun := α.hom.app W
                map_add' := ha W
                map_smul' := hs W }
          naturality := by
            intro W V f
            ext x
            exact CategoryTheory.congr_fun (α.hom.naturality f) x } }
  refine ⟨f, ?_⟩
  simp only [eqToHom_refl, Category.id_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Restricting scalars commutes with an algebraic inverse image along a compatible
ring square. The underlying morphism is the identity between the two presentations
of the same inverse image of a sheaf of sets.

Source: Stacks Project, Modules on Sites, Tags 03D2 and 03DA
(blueprint: lem-pur-inverse-image-scalar-restriction-comparison).

Proof: Transport the identity of underlying inverse-image sheaves through the two
specified underlying isomorphisms. To verify additivity, apply the two graph equations
to the product of the underlying module sheaf with itself, using preservation of this
product by inverse image. For scalar multiplication use the product of the underlying
ring sheaf and module sheaf; compatibility of the ring square identifies the scalar
on the two sides. The resulting section maps are linear and natural. Their underlying
maps are isomorphisms, so reflection of isomorphisms by the underlying-sheaf functor
gives a natural isomorphism. Cancelling the second underlying isomorphism gives the
asserted normalization. -/
theorem exists_comparison
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    {L : Sheaf J (Type w) ⥤ Sheaf K (Type w)} [PreservesFiniteLimits L]
    {R S : Sheaf J CommRingCat.{w}} {RU SU : Sheaf K CommRingCat.{w}}
    (A : AlgebraicInverseImage L R RU) (B : AlgebraicInverseImage L S SU)
    (a : R ⟶ S) (b : RU ⟶ SU)
    (hc : L.map ((sheafCompose J (CategoryTheory.forget CommRingCat.{w})).map a) ≫
        B.ringUnderlying.hom =
      A.ringUnderlying.hom ≫ (sheafCompose K (CategoryTheory.forget CommRingCat.{w})).map b) :
    ∃ ρ : B.modules ⋙ restrictScalars
          ((sheafCompose K (forget₂ CommRingCat.{w} RingCat.{w})).map b) ≅
        restrictScalars ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map a) ⋙ A.modules,
      ∀ M : SheafOfModules.{w}
        ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj S),
        (toSheaf _ ⋙ sheafCompose K (CategoryTheory.forget AddCommGrpCat.{w})).map (ρ.hom.app M) ≫
            A.moduleUnderlying.hom.app ((restrictScalars
              ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map a)).obj M) =
          B.moduleUnderlying.hom.app M := by
  let resY := restrictScalars ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map a)
  let resX := restrictScalars ((sheafCompose K (forget₂ CommRingCat.{w} RingCat.{w})).map b)
  have hex (M : SheafOfModules.{w} (base S)) :=
    inverse_change_hom A B a b rfl (by simpa using hc.symm) M
  let f (M : SheafOfModules.{w} (base S)) := (hex M).choose
  have hf (M : SheafOfModules.{w} (base S)) :
      (sets RU).map (f M) =
        A.moduleUnderlying.hom.app (resY.obj M) ≫ B.moduleUnderlying.inv.app M := by
    simpa using (hex M).choose_spec
  have hi (M : SheafOfModules.{w} (base S)) : IsIso (f M) := by
    have : IsIso ((sets RU).map (f M)) := by rw [hf]; infer_instance
    exact isIso_of_reflects_iso _ (sets RU)
  let ρ : resY ⋙ A.modules ≅ B.modules ⋙ resX :=
    NatIso.ofComponents (fun M ↦ asIso (f M)) (by
      intro M N h
      apply (sets RU).map_injective
      simp only [Functor.map_comp, asIso_hom, hf, Category.assoc]
      change (sets RU).map (A.modules.map (resY.map h)) ≫
          A.moduleUnderlying.hom.app (resY.obj N) ≫ B.moduleUnderlying.inv.app N =
        A.moduleUnderlying.hom.app (resY.obj M) ≫ B.moduleUnderlying.inv.app M ≫
          (sets SU).map (B.modules.map h)
      calc
        _ = A.moduleUnderlying.hom.app (resY.obj M) ≫
            L.map ((sets R).map (resY.map h)) ≫ B.moduleUnderlying.inv.app N :=
          A.moduleUnderlying.hom.naturality_assoc (resY.map h) _
        _ = _ := by
          apply congrArg (A.moduleUnderlying.hom.app (resY.obj M) ≫ ·)
          exact B.moduleUnderlying.inv.naturality h)
  refine ⟨ρ.symm, ?_⟩
  intro M
  apply (cancel_epi ((sets RU).map (ρ.hom.app M))).1
  simp only [Iso.symm_hom, ← Functor.map_comp_assoc, Iso.hom_inv_id_app]
  change A.moduleUnderlying.hom.app (resY.obj M) =
    (sets RU).map (f M) ≫ B.moduleUnderlying.hom.app M
  rw [hf, Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]

end SheafOfModules.InverseImageScalarRestriction
