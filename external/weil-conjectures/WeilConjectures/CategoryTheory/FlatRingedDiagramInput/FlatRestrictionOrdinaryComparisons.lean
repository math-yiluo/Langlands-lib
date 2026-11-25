/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.FlatRingedDiagramInput.FlatRingedDiagramRestrictionDefs
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Ordinary coefficient comparison isomorphisms

Source: Stacks Project, Modules on Sites, Tag 03D3.
(blueprint: lem-weil-pbc-flat-restriction-ordinary-comparisons).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.FlatRingedDiagramInput

open MonoidalCategory
open CartesianMonoidalCategory

private noncomputable abbrev base
    {T : Type u} [SmallCategory T] {τ : GrothendieckTopology T}
    (R : Sheaf τ CommRingCat.{u}) :=
  (sheafCompose τ (forget₂ CommRingCat RingCat)).obj R

private noncomputable abbrev sets
    {T : Type u} [SmallCategory T] {τ : GrothendieckTopology T}
    (R : Sheaf τ CommRingCat.{u}) :=
  SheafOfModules.toSheaf (base R) ⋙ sheafCompose τ (forget AddCommGrpCat)

private noncomputable abbrev ringSets
    {T : Type u} [SmallCategory T] {τ : GrothendieckTopology T}
    (R : Sheaf τ CommRingCat.{u}) := (sheafCompose τ (forget CommRingCat)).obj R

private noncomputable def addMap
    {T : Type u} [SmallCategory T] {τ : GrothendieckTopology T}
    {R : Sheaf τ CommRingCat.{u}} (M : SheafOfModules.{u} (base R)) :
    (sets R).obj M ⊗ (sets R).obj M ⟶ (sets R).obj M :=
  ⟨{ app := fun W ↦ ↾(fun z ↦ @Add.add (M.val.obj W) inferInstance z.1 z.2)
     naturality := by intro W V f; ext z; exact ((M.val.map f).hom.map_add _ _).symm }⟩

private noncomputable def smulMap
    {T : Type u} [SmallCategory T] {τ : GrothendieckTopology T}
    {R : Sheaf τ CommRingCat.{u}} (M : SheafOfModules.{u} (base R)) :
    ringSets R ⊗ (sets R).obj M ⟶ (sets R).obj M :=
  ⟨{ app := fun W ↦ ↾(fun z ↦ @SMul.smul (R.obj.obj W) (M.val.obj W)
        inferInstance z.1 z.2)
     naturality := by intro W V f; ext z; exact (M.val.map_smul f z.1 z.2).symm }⟩

private noncomputable def pairPreimage
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {K : GrothendieckTopology C} {H : GrothendieckTopology D}
    (L : Sheaf K (Type u) ⥤ Sheaf H (Type u)) [PreservesFiniteLimits L]
    (X Y : Sheaf K (Type u)) (W : Dᵒᵖ)
    (x : (L.obj X).obj.obj W) (y : (L.obj Y).obj.obj W) :
    (L.obj (X ⊗ Y)).obj.obj W :=
  (inv (CartesianMonoidalCategory.prodComparison L X Y)).hom.app W (x, y)

private theorem pairPreimage_fst
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {K : GrothendieckTopology C} {H : GrothendieckTopology D}
    (L : Sheaf K (Type u) ⥤ Sheaf H (Type u)) [PreservesFiniteLimits L]
    (X Y : Sheaf K (Type u)) (W : Dᵒᵖ)
    (x : (L.obj X).obj.obj W) (y : (L.obj Y).obj.obj W) :
    (L.map (CartesianMonoidalCategory.fst X Y)).hom.app W
      (pairPreimage L X Y W x y) = x := by
  exact congrArg (fun f ↦ f.hom.app W (x, y))
    (CartesianMonoidalCategory.inv_prodComparison_map_fst L X Y)

private theorem pairPreimage_snd
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {K : GrothendieckTopology C} {H : GrothendieckTopology D}
    (L : Sheaf K (Type u) ⥤ Sheaf H (Type u)) [PreservesFiniteLimits L]
    (X Y : Sheaf K (Type u)) (W : Dᵒᵖ)
    (x : (L.obj X).obj.obj W) (y : (L.obj Y).obj.obj W) :
    (L.map (CartesianMonoidalCategory.snd X Y)).hom.app W
      (pairPreimage L X Y W x y) = y := by
  exact congrArg (fun f ↦ f.hom.app W (x, y))
    (CartesianMonoidalCategory.inv_prodComparison_map_snd L X Y)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- Comparing the two scalar actions unfolds the underlying-set restriction presentations.
private theorem inverse_change_hom
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {K : GrothendieckTopology C} {H : GrothendieckTopology D}
    {L L' : Sheaf K (Type u) ⥤ Sheaf H (Type u)} [PreservesFiniteLimits L]
    {R S : Sheaf K CommRingCat.{u}} {RU SU : Sheaf H CommRingCat.{u}}
    (A : SheafOfModules.AlgebraicInverseImage L R RU)
    (B : SheafOfModules.AlgebraicInverseImage L' S SU)
    (a : R ⟶ S) (b : RU ⟶ SU) (h : L = L')
    (hc : A.ringUnderlying.hom ≫ (sheafCompose H (forget CommRingCat)).map b =
      L.map ((sheafCompose K (forget CommRingCat)).map a) ≫
        eqToHom (congrArg (fun F ↦ F.obj (ringSets S)) h) ≫ B.ringUnderlying.hom)
    (M : SheafOfModules.{u} (base S)) :
    ∃ f : A.modules.obj ((SheafOfModules.restrictScalars
        ((sheafCompose K (forget₂ CommRingCat RingCat)).map a)).obj M) ⟶
        (SheafOfModules.restrictScalars
          ((sheafCompose H (forget₂ CommRingCat RingCat)).map b)).obj (B.modules.obj M),
      (sets RU).map f =
        A.moduleUnderlying.hom.app _ ≫
          eqToHom (congrArg (fun F ↦ F.obj ((sets S).obj M)) h) ≫
          B.moduleUnderlying.inv.app M := by
  subst L'
  let MR := (SheafOfModules.restrictScalars
    ((sheafCompose K (forget₂ CommRingCat RingCat)).map a)).obj M
  let N := A.modules.obj MR
  let N' := (SheafOfModules.restrictScalars
    ((sheafCompose H (forget₂ CommRingCat RingCat)).map b)).obj (B.modules.obj M)
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
        (CartesianMonoidalCategory.fst Y X ≫ (sheafCompose K (forget CommRingCat)).map a)
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
        (sheafCompose K (forget CommRingCat)).map a)).hom.app W z) = b.hom.app W r := by
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
        (CartesianMonoidalCategory.fst Y X ≫ (sheafCompose K (forget CommRingCat)).map a)
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

private theorem paste_naturality
    {T : Type*} [Category T]
    {X₁ X₂ Y₁ Y₂ Z₁ Z₂ W₁ W₂ : T}
    {f : X₁ ⟶ X₂} {g : Y₁ ⟶ Y₂} {h : Z₁ ⟶ Z₂} {i : W₁ ⟶ W₂}
    {a₁ : X₁ ⟶ Y₁} {a₂ : X₂ ⟶ Y₂}
    {b₁ : Y₁ ⟶ Z₁} {b₂ : Y₂ ⟶ Z₂}
    {c₁ : Z₁ ⟶ W₁} {c₂ : Z₂ ⟶ W₂}
    (ha : f ≫ a₂ = a₁ ≫ g) (hb : g ≫ b₂ = b₁ ≫ h)
    (hc : h ≫ c₂ = c₁ ≫ i) :
    f ≫ (a₂ ≫ b₂ ≫ c₂) = (a₁ ≫ b₁ ≫ c₁) ≫ i := by
  calc
    _ = a₁ ≫ g ≫ b₂ ≫ c₂ := by rw [← Category.assoc, ha, Category.assoc]
    _ = a₁ ≫ b₁ ≫ h ≫ c₂ := by
      rw [← Category.assoc g, hb, Category.assoc]
    _ = _ := by rw [hc]; simp only [Category.assoc]

section

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {K : GrothendieckTopology C} {H : GrothendieckTopology D}
  (x : FlatRingedDiagramInput K H) (J : Type u) [SmallCategory J]

/-- The actual termwise restriction of scalars at V.
Source: Stacks 03D3 (blueprint: def-weil-pbc-flat-ringed-diagram-input). -/
noncomputable abbrev restrictV : x.diagramsSV J ⥤ x.diagramsRV J :=
  (Functor.whiskeringRight J _ _).obj (SheafOfModules.restrictScalars.{u}
    ((sheafCompose K (forget₂ CommRingCat RingCat)).map x.aV))

/-- The actual termwise restriction of scalars at U.
Source: Stacks 03D3 (blueprint: def-weil-pbc-flat-ringed-diagram-input). -/
noncomputable abbrev restrictU : x.diagramsSU J ⥤ x.diagramsRU J :=
  (Functor.whiskeringRight J _ _).obj (SheafOfModules.restrictScalars.{u}
    ((sheafCompose H (forget₂ CommRingCat RingCat)).map x.aU))

end

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- Naturality compares the two presentations of restriction on underlying sheaves.
private theorem inverse_comparison
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {K : GrothendieckTopology C} {H : GrothendieckTopology D}
    (x : FlatRingedDiagramInput K H) (J : Type u) [SmallCategory J] :
    ∃ b0 : x.inverseS J ⋙ x.restrictU J ≅ x.restrictV J ⋙ x.inverseR J,
      ∀ (M : x.diagramsSV J) (j : J),
        HEq ((sets x.RU).map ((b0.hom.app M).app j))
          (x.S.inverse.moduleUnderlying.hom.app (M.obj j) ≫
            eqToHom (congrArg (fun F ↦ F.obj ((sets x.SV).obj (M.obj j)))
              x.sameInverse.symm) ≫
            x.R.inverse.moduleUnderlying.inv.app (((x.restrictV J).obj M).obj j)) := by
  classical
  have : PreservesFiniteLimits x.R.morphism.inverse := x.R.morphism.leftExact
  let resU := SheafOfModules.restrictScalars
    ((sheafCompose H (forget₂ CommRingCat RingCat)).map x.aU)
  let resV := SheafOfModules.restrictScalars
    ((sheafCompose K (forget₂ CommRingCat RingCat)).map x.aV)
  have hex (M : SheafOfModules.{u} (base x.SV)) := inverse_change_hom
    x.R.inverse x.S.inverse x.aV x.aU x.sameInverse x.coherent M
  let f (M : SheafOfModules.{u} (base x.SV)) := (hex M).choose
  have hf (M : SheafOfModules.{u} (base x.SV)) :
      (sets x.RU).map (f M) =
        x.R.inverse.moduleUnderlying.hom.app (resV.obj M) ≫
          eqToHom (congrArg (fun F ↦ F.obj ((sets x.SV).obj M)) x.sameInverse) ≫
          x.S.inverse.moduleUnderlying.inv.app M := (hex M).choose_spec
  have hfi (M : SheafOfModules.{u} (base x.SV)) : IsIso (f M) := by
    have : IsIso ((sets x.RU).map (f M)) := by rw [hf]; infer_instance
    exact isIso_of_reflects_iso (f M) (sets x.RU)
  let β : resV ⋙ x.R.inverse.modules ⟶ x.S.inverse.modules ⋙ resU :=
    { app := f
      naturality := by
        intro M N g
        apply (sets x.RU).map_injective
        change (sets x.RU).map (x.R.inverse.modules.map (resV.map g) ≫ f N) =
          (sets x.RU).map (f M ≫ resU.map (x.S.inverse.modules.map g))
        rw [Functor.map_comp, Functor.map_comp, hf M, hf N]
        have hR := x.R.inverse.moduleUnderlying.hom.naturality (resV.map g)
        have hS := x.S.inverse.moduleUnderlying.inv.naturality g
        have he := (eqToHom (congrArg (fun F ↦ F) x.sameInverse) :
          x.R.morphism.inverse ⟶ x.S.morphism.inverse).naturality ((sets x.SV).map g)
        change (sets x.RU).map (x.R.inverse.modules.map (resV.map g)) ≫
          x.R.inverse.moduleUnderlying.hom.app (resV.obj N) =
          x.R.inverse.moduleUnderlying.hom.app (resV.obj M) ≫
            x.R.morphism.inverse.map ((sets x.SV).map g) at hR
        change x.S.morphism.inverse.map ((sets x.SV).map g) ≫
          x.S.inverse.moduleUnderlying.inv.app N =
          x.S.inverse.moduleUnderlying.inv.app M ≫
            (sets x.RU).map (resU.map (x.S.inverse.modules.map g)) at hS
        simp only [eqToHom_app] at he
        change x.R.morphism.inverse.map ((sets x.SV).map g) ≫
            eqToHom (congrArg (fun F ↦ F.obj ((sets x.SV).obj N)) x.sameInverse) =
          eqToHom (congrArg (fun F ↦ F.obj ((sets x.SV).obj M)) x.sameInverse) ≫
            x.S.morphism.inverse.map ((sets x.SV).map g) at he
        exact paste_naturality hR he hS }
  let B : x.restrictV J ⋙ x.inverseR J ≅ x.inverseS J ⋙ x.restrictU J :=
    NatIso.ofComponents (fun M ↦ NatIso.ofComponents (fun j ↦ asIso (f (M.obj j)))
      (fun g ↦ β.naturality (M.map g)))
      (by intro M N g; ext j : 2; exact β.naturality (g.app j))
  refine ⟨B.symm, ?_⟩
  intro M j
  apply heq_of_eq
  have hi := hf (M.obj j)
  have hinv : (sets x.RU).map (inv (f (M.obj j))) =
      x.S.inverse.moduleUnderlying.hom.app (M.obj j) ≫
        eqToHom (congrArg (fun F ↦ F.obj ((sets x.SV).obj (M.obj j)))
          x.sameInverse.symm) ≫
        x.R.inverse.moduleUnderlying.inv.app (resV.obj (M.obj j)) := by
    apply (cancel_epi ((sets x.RU).map (f (M.obj j)))).mp
    rw [← Functor.map_comp, IsIso.hom_inv_id, Functor.map_id, hi]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc, eqToHom_trans_assoc,
      eqToHom_refl, Category.id_comp]
    exact (x.R.inverse.moduleUnderlying.hom_inv_id_app (resV.obj (M.obj j))).symm
  exact hinv

private theorem adjunct_mate
    {A B E F : Type*} [Category A] [Category B] [Category E] [Category F]
    {LS : A ⥤ B} {FS : B ⥤ A} {LR : E ⥤ F} {FR : F ⥤ E}
    (aS : LS ⊣ FS) (aR : LR ⊣ FR) (rV : A ⥤ E) (rU : B ⥤ F)
    (b : LS ⋙ rU ≅ rV ⋙ LR) (M : A) (N : B) (t : LS.obj M ⟶ N) :
    aR.homEquiv (rV.obj M) (rU.obj N) (b.inv.app M ≫ rU.map t) =
      rV.map (aS.homEquiv M N t) ≫
        (mateEquiv aS aR (TwoSquare.mk _ _ _ _ b.inv)).app N := by
  let d := mateEquiv aS aR (TwoSquare.mk _ _ _ _ b.inv)
  have h := unit_mateEquiv aS aR (TwoSquare.mk _ _ _ _ b.inv) M
  change rV.map (aS.unit.app M) ≫ d.app (LS.obj M) =
    aR.unit.app (rV.obj M) ≫ FR.map (b.inv.app M) at h
  rw [aR.homEquiv_unit, FR.map_comp, ← Category.assoc, ← h, Category.assoc]
  have hd : d.app (LS.obj M) ≫ FR.map (rU.map t) =
      rV.map (FS.map t) ≫ d.app N := d.naturality t |>.symm
  rw [hd]
  rw [aS.homEquiv_unit, rV.map_comp, Category.assoc]

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {K : GrothendieckTopology C} {H : GrothendieckTopology D}
  (x : FlatRingedDiagramInput K H) (J : Type u) [SmallCategory J]

-- Restriction preserves the underlying sheaf but changes its bundled scalar action.
end CategoryTheory.FlatRingedDiagramInput
