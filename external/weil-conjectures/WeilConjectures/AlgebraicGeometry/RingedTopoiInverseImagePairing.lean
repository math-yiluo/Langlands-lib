/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import WeilConjectures.AlgebraicGeometry.RingedTopoiTensorSections
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction

/-! # Canonical pairing on the supplied algebraic inverse image
Source: Stacks Project, Modules on Sites, Tag 03EL.
(auxiliary; not a blueprint node).
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace SheafOfModules.RingedTensor
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {C D : Type u} [Category.{u} C] [Category.{u} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/-- The pure tensor pairing, viewed in the cartesian category of set sheaves.
Source: Stacks Project, Modules on Sites, Tag 03EL
(auxiliary; not a blueprint node). -/
noncomputable def pureSheaf (R : Sheaf J CommRingCat.{u})
    (M N : SheafOfModules.{u} (ringSheaf R)) :
    (underlying R).obj M ⊗ (underlying R).obj N ⟶
      (underlying R).obj ((monoidalCategory R).tensorObj M N) :=
  ⟨{ app := fun W ↦ ↾(fun p ↦ pure R M N W p.1 p.2)
     naturality := by
       intro V W i
       ext p
       exact (pure_restrict R M N i p.1 p.2).symm }⟩

private noncomputable def imageBinary
    (F : Sheaf J (Type u) ⥤ Sheaf K (Type u)) [F.Monoidal]
    {X Y Z : Sheaf J (Type u)} {A B E : Sheaf K (Type u)}
    (eX : A ≅ F.obj X) (eY : B ≅ F.obj Y) (eZ : E ≅ F.obj Z)
    (f : X ⊗ Y ⟶ Z) : A ⊗ B ⟶ E :=
  (eX.hom ⊗ₘ eY.hom) ≫ Functor.LaxMonoidal.μ F X Y ≫ F.map f ≫ eZ.inv

private theorem imageBinary_graph
    (F : Sheaf J (Type u) ⥤ Sheaf K (Type u)) [F.Monoidal]
    {X Y Z T : Sheaf J (Type u)} {A B E : Sheaf K (Type u)}
    (eX : A ≅ F.obj X) (eY : B ≅ F.obj Y) (eZ : E ≅ F.obj Z)
    (f : X ⊗ Y ⟶ Z) (x : T ⟶ X) (y : T ⟶ Y) :
    F.map (CartesianMonoidalCategory.lift x y ≫ f) ≫ eZ.inv =
      CartesianMonoidalCategory.lift (F.map x ≫ eX.inv) (F.map y ≫ eY.inv) ≫
        imageBinary F eX eY eZ f := by
  dsimp only [imageBinary]
  rw [F.map_comp, ← Category.assoc, ← Functor.Monoidal.lift_μ]
  simp only [Category.assoc, CartesianMonoidalCategory.lift_map,
    Iso.inv_hom_id, Category.comp_id]

private theorem imageBinary_graph_apply
    (F : Sheaf J (Type u) ⥤ Sheaf K (Type u)) [F.Monoidal]
    {X Y Z T : Sheaf J (Type u)} {A B E : Sheaf K (Type u)}
    (eX : A ≅ F.obj X) (eY : B ≅ F.obj Y) (eZ : E ≅ F.obj Z)
    (f : X ⊗ Y ⟶ Z) (x : T ⟶ X) (y : T ⟶ Y)
    (W : Dᵒᵖ) (t : (F.obj T).obj.obj W) :
    (F.map (CartesianMonoidalCategory.lift x y ≫ f) ≫ eZ.inv).hom.app W t =
      (imageBinary F eX eY eZ f).hom.app W
        ((F.map x ≫ eX.inv).hom.app W t, (F.map y ≫ eY.inv).hom.app W t) :=
  congrArg (fun k ↦ k.hom.app W t) (imageBinary_graph F eX eY eZ f x y)

private noncomputable def tripleSection
    (F : Sheaf J (Type u) ⥤ Sheaf K (Type u)) [F.Monoidal]
    (X Y Z : Sheaf J (Type u)) (W : Dᵒᵖ)
    (x : (F.obj X).obj.obj W) (y : (F.obj Y).obj.obj W) (z : (F.obj Z).obj.obj W) :
    (F.obj ((X ⊗ Y) ⊗ Z)).obj.obj W :=
  (Functor.LaxMonoidal.μ F (X ⊗ Y) Z).hom.app W
    ((Functor.LaxMonoidal.μ F X Y).hom.app W (x, y), z)

private theorem tripleSection_fst_fst
    (F : Sheaf J (Type u) ⥤ Sheaf K (Type u)) [F.Monoidal]
    (X Y Z : Sheaf J (Type u)) (W : Dᵒᵖ)
    (x : (F.obj X).obj.obj W) (y : (F.obj Y).obj.obj W) (z : (F.obj Z).obj.obj W) :
    (F.map (CartesianMonoidalCategory.fst (X ⊗ Y) Z ≫
      CartesianMonoidalCategory.fst X Y)).hom.app W (tripleSection F X Y Z W x y z) = x := by
  have h := congrArg (fun k ↦ k.hom.app W
    ((Functor.LaxMonoidal.μ F X Y).hom.app W (x, y), z))
      (Functor.Monoidal.μ_fst F (X ⊗ Y) Z)
  have h' := congrArg (fun k ↦ k.hom.app W (x, y)) (Functor.Monoidal.μ_fst F X Y)
  change (F.map (CartesianMonoidalCategory.fst (X ⊗ Y) Z)).hom.app W
    (tripleSection F X Y Z W x y z) =
      (Functor.LaxMonoidal.μ F X Y).hom.app W (x, y) at h
  change (F.map (CartesianMonoidalCategory.fst X Y)).hom.app W
    ((Functor.LaxMonoidal.μ F X Y).hom.app W (x, y)) = x at h'
  rw [F.map_comp]
  exact (congrArg ((F.map (CartesianMonoidalCategory.fst X Y)).hom.app W) h).trans h'

private theorem tripleSection_fst_snd
    (F : Sheaf J (Type u) ⥤ Sheaf K (Type u)) [F.Monoidal]
    (X Y Z : Sheaf J (Type u)) (W : Dᵒᵖ)
    (x : (F.obj X).obj.obj W) (y : (F.obj Y).obj.obj W) (z : (F.obj Z).obj.obj W) :
    (F.map (CartesianMonoidalCategory.fst (X ⊗ Y) Z ≫
      CartesianMonoidalCategory.snd X Y)).hom.app W (tripleSection F X Y Z W x y z) = y := by
  have h := congrArg (fun k ↦ k.hom.app W
    ((Functor.LaxMonoidal.μ F X Y).hom.app W (x, y), z))
      (Functor.Monoidal.μ_fst F (X ⊗ Y) Z)
  have h' := congrArg (fun k ↦ k.hom.app W (x, y)) (Functor.Monoidal.μ_snd F X Y)
  change (F.map (CartesianMonoidalCategory.fst (X ⊗ Y) Z)).hom.app W
    (tripleSection F X Y Z W x y z) =
      (Functor.LaxMonoidal.μ F X Y).hom.app W (x, y) at h
  change (F.map (CartesianMonoidalCategory.snd X Y)).hom.app W
    ((Functor.LaxMonoidal.μ F X Y).hom.app W (x, y)) = y at h'
  rw [F.map_comp]
  exact (congrArg ((F.map (CartesianMonoidalCategory.snd X Y)).hom.app W) h).trans h'

private theorem tripleSection_snd
    (F : Sheaf J (Type u) ⥤ Sheaf K (Type u)) [F.Monoidal]
    (X Y Z : Sheaf J (Type u)) (W : Dᵒᵖ)
    (x : (F.obj X).obj.obj W) (y : (F.obj Y).obj.obj W) (z : (F.obj Z).obj.obj W) :
    (F.map (CartesianMonoidalCategory.snd (X ⊗ Y) Z)).hom.app W
      (tripleSection F X Y Z W x y z) = z :=
  congrArg (fun k ↦ k.hom.app W
    ((Functor.LaxMonoidal.μ F X Y).hom.app W (x, y), z))
      (Functor.Monoidal.μ_snd F (X ⊗ Y) Z)

private theorem tripleSections
    (F : Sheaf J (Type u) ⥤ Sheaf K (Type u)) [F.Monoidal]
    {X Y Z : Sheaf J (Type u)} {A B E : Sheaf K (Type u)}
    (eX : A ≅ F.obj X) (eY : B ≅ F.obj Y) (eZ : E ≅ F.obj Z)
    (W : Dᵒᵖ) (a : A.obj.obj W) (b : B.obj.obj W) (c : E.obj.obj W) :
    ∃ t : (F.obj ((X ⊗ Y) ⊗ Z)).obj.obj W,
      (F.map (CartesianMonoidalCategory.fst (X ⊗ Y) Z ≫
        CartesianMonoidalCategory.fst X Y) ≫ eX.inv).hom.app W t = a ∧
      (F.map (CartesianMonoidalCategory.fst (X ⊗ Y) Z ≫
        CartesianMonoidalCategory.snd X Y) ≫ eY.inv).hom.app W t = b ∧
      (F.map (CartesianMonoidalCategory.snd (X ⊗ Y) Z) ≫ eZ.inv).hom.app W t = c := by
  refine ⟨tripleSection F X Y Z W (eX.hom.hom.app W a)
    (eY.hom.hom.app W b) (eZ.hom.hom.app W c), ?_, ?_, ?_⟩
  · exact (congrArg (eX.inv.hom.app W)
      (tripleSection_fst_fst F X Y Z W _ _ _)).trans
        (congrArg (fun k ↦ k.hom.app W a) eX.hom_inv_id)
  · exact (congrArg (eY.inv.hom.app W)
      (tripleSection_fst_snd F X Y Z W _ _ _)).trans
        (congrArg (fun k ↦ k.hom.app W b) eY.hom_inv_id)
  · exact (congrArg (eZ.inv.hom.app W)
      (tripleSection_snd F X Y Z W _ _ _)).trans
        (congrArg (fun k ↦ k.hom.app W c) eZ.hom_inv_id)

private theorem transportedPairing_add_left
    (R : Sheaf J CommRingCat.{u}) (RI : Sheaf K CommRingCat.{u})
    (F : Sheaf J (Type u) ⥤ Sheaf K (Type u)) [F.Monoidal]
    (I : AlgebraicInverseImage F R RI)
    (M N : SheafOfModules.{u} (ringSheaf R)) (W : Dᵒᵖ)
    (a b : (I.modules.obj M).val.obj W) (c : (I.modules.obj N).val.obj W) :
    let β := imageBinary F (I.moduleUnderlying.app M) (I.moduleUnderlying.app N)
      (I.moduleUnderlying.app ((monoidalCategory R).tensorObj M N)) (pureSheaf R M N)
    β.hom.app W (a + b, c) =
      (show (I.modules.obj ((monoidalCategory R).tensorObj M N)).val.obj W from
        β.hom.app W (a, c)) +
      (show (I.modules.obj ((monoidalCategory R).tensorObj M N)).val.obj W from
        β.hom.app W (b, c)) := by
  let X := (underlying R).obj M
  let Y := (underlying R).obj N
  let P := (X ⊗ X) ⊗ Y
  let x : P ⟶ X := CartesianMonoidalCategory.fst (X ⊗ X) Y ≫
    CartesianMonoidalCategory.fst X X
  let y : P ⟶ X := CartesianMonoidalCategory.fst (X ⊗ X) Y ≫
    CartesianMonoidalCategory.snd X X
  let n : P ⟶ Y := CartesianMonoidalCategory.snd (X ⊗ X) Y
  let s : P ⟶ X := CartesianMonoidalCategory.lift x y ≫ GeometricConstruction.addition R M
  let p : P ⟶ (underlying R).obj ((monoidalCategory R).tensorObj M N) :=
    CartesianMonoidalCategory.lift s n ≫ pureSheaf R M N
  let q : P ⟶ (underlying R).obj ((monoidalCategory R).tensorObj M N) :=
    CartesianMonoidalCategory.lift x n ≫ pureSheaf R M N
  let r : P ⟶ (underlying R).obj ((monoidalCategory R).tensorObj M N) :=
    CartesianMonoidalCategory.lift y n ≫ pureSheaf R M N
  obtain ⟨t, hx, hy, hn⟩ := tripleSections F (I.moduleUnderlying.app M)
    (I.moduleUnderlying.app M) (I.moduleUnderlying.app N) W a b c
  have hs := I.moduleAdd M P x y s (fun _ _ ↦ rfl) W t
  change (F.map s ≫ I.moduleUnderlying.inv.app M).hom.app W t = _ at hs
  change (F.map x ≫ I.moduleUnderlying.inv.app M).hom.app W t = a at hx
  change (F.map y ≫ I.moduleUnderlying.inv.app M).hom.app W t = b at hy
  change (F.map n ≫ I.moduleUnderlying.inv.app N).hom.app W t = c at hn
  have hs' := hs.trans (congrArg₂ (fun (v w : (I.modules.obj M).val.obj W) ↦ v + w) hx hy)
  have hp := I.moduleAdd ((monoidalCategory R).tensorObj M N) P q r p
    (fun U v ↦ (pureBilin R M N U).map_add₂ _ _ _) W t
  have h₁ := imageBinary_graph_apply F (I.moduleUnderlying.app M)
    (I.moduleUnderlying.app N) (I.moduleUnderlying.app ((monoidalCategory R).tensorObj M N))
    (pureSheaf R M N) s n W t
  have h₂ := imageBinary_graph_apply F (I.moduleUnderlying.app M)
    (I.moduleUnderlying.app N) (I.moduleUnderlying.app ((monoidalCategory R).tensorObj M N))
    (pureSheaf R M N) x n W t
  have h₃ := imageBinary_graph_apply F (I.moduleUnderlying.app M)
    (I.moduleUnderlying.app N) (I.moduleUnderlying.app ((monoidalCategory R).tensorObj M N))
    (pureSheaf R M N) y n W t
  let β := imageBinary F (I.moduleUnderlying.app M) (I.moduleUnderlying.app N)
    (I.moduleUnderlying.app ((monoidalCategory R).tensorObj M N)) (pureSheaf R M N)
  let B (v : (I.modules.obj M).val.obj W) (w : (I.modules.obj N).val.obj W) :
      (I.modules.obj ((monoidalCategory R).tensorObj M N)).val.obj W := β.hom.app W (v, w)
  have h₁' := h₁.trans (congrArg₂ B hs' hn)
  have h₂' := h₂.trans (congrArg₂ B hx hn)
  have h₃' := h₃.trans (congrArg₂ B hy hn)
  exact h₁'.symm.trans (hp.trans
    (congrArg₂ (fun (v w : (I.modules.obj ((monoidalCategory R).tensorObj M N)).val.obj W) ↦
      v + w) h₂' h₃'))

private theorem transportedPairing_add_right
    (R : Sheaf J CommRingCat.{u}) (RI : Sheaf K CommRingCat.{u})
    (F : Sheaf J (Type u) ⥤ Sheaf K (Type u)) [F.Monoidal]
    (I : AlgebraicInverseImage F R RI)
    (M N : SheafOfModules.{u} (ringSheaf R)) (W : Dᵒᵖ)
    (a b : (I.modules.obj N).val.obj W) (c : (I.modules.obj M).val.obj W) :
    let β := imageBinary F (I.moduleUnderlying.app M) (I.moduleUnderlying.app N)
      (I.moduleUnderlying.app ((monoidalCategory R).tensorObj M N)) (pureSheaf R M N)
    β.hom.app W (c, a + b) =
      (show (I.modules.obj ((monoidalCategory R).tensorObj M N)).val.obj W from
        β.hom.app W (c, a)) +
      (show (I.modules.obj ((monoidalCategory R).tensorObj M N)).val.obj W from
        β.hom.app W (c, b)) := by
  let X := (underlying R).obj N
  let Y := (underlying R).obj M
  let P := (X ⊗ X) ⊗ Y
  let x : P ⟶ X := CartesianMonoidalCategory.fst (X ⊗ X) Y ≫
    CartesianMonoidalCategory.fst X X
  let y : P ⟶ X := CartesianMonoidalCategory.fst (X ⊗ X) Y ≫
    CartesianMonoidalCategory.snd X X
  let n : P ⟶ Y := CartesianMonoidalCategory.snd (X ⊗ X) Y
  let s : P ⟶ X := CartesianMonoidalCategory.lift x y ≫ GeometricConstruction.addition R N
  let p : P ⟶ (underlying R).obj ((monoidalCategory R).tensorObj M N) :=
    CartesianMonoidalCategory.lift n s ≫ pureSheaf R M N
  let q : P ⟶ (underlying R).obj ((monoidalCategory R).tensorObj M N) :=
    CartesianMonoidalCategory.lift n x ≫ pureSheaf R M N
  let r : P ⟶ (underlying R).obj ((monoidalCategory R).tensorObj M N) :=
    CartesianMonoidalCategory.lift n y ≫ pureSheaf R M N
  obtain ⟨t, hx, hy, hn⟩ := tripleSections F (I.moduleUnderlying.app N)
    (I.moduleUnderlying.app N) (I.moduleUnderlying.app M) W a b c
  have hs := I.moduleAdd N P x y s (fun _ _ ↦ rfl) W t
  change (F.map s ≫ I.moduleUnderlying.inv.app N).hom.app W t = _ at hs
  change (F.map x ≫ I.moduleUnderlying.inv.app N).hom.app W t = a at hx
  change (F.map y ≫ I.moduleUnderlying.inv.app N).hom.app W t = b at hy
  change (F.map n ≫ I.moduleUnderlying.inv.app M).hom.app W t = c at hn
  have hs' := hs.trans (congrArg₂ (fun (v w : (I.modules.obj N).val.obj W) ↦ v + w) hx hy)
  have hp := I.moduleAdd ((monoidalCategory R).tensorObj M N) P q r p
    (fun U v ↦ (pureBilin R M N U _).map_add _ _) W t
  have h₁ := imageBinary_graph_apply F (I.moduleUnderlying.app M)
    (I.moduleUnderlying.app N) (I.moduleUnderlying.app ((monoidalCategory R).tensorObj M N))
    (pureSheaf R M N) n s W t
  have h₂ := imageBinary_graph_apply F (I.moduleUnderlying.app M)
    (I.moduleUnderlying.app N) (I.moduleUnderlying.app ((monoidalCategory R).tensorObj M N))
    (pureSheaf R M N) n x W t
  have h₃ := imageBinary_graph_apply F (I.moduleUnderlying.app M)
    (I.moduleUnderlying.app N) (I.moduleUnderlying.app ((monoidalCategory R).tensorObj M N))
    (pureSheaf R M N) n y W t
  let β := imageBinary F (I.moduleUnderlying.app M) (I.moduleUnderlying.app N)
    (I.moduleUnderlying.app ((monoidalCategory R).tensorObj M N)) (pureSheaf R M N)
  let B (v : (I.modules.obj M).val.obj W) (w : (I.modules.obj N).val.obj W) :
      (I.modules.obj ((monoidalCategory R).tensorObj M N)).val.obj W := β.hom.app W (v, w)
  have h₁' := h₁.trans (congrArg₂ B hn hs')
  have h₂' := h₂.trans (congrArg₂ B hn hx)
  have h₃' := h₃.trans (congrArg₂ B hn hy)
  exact h₁'.symm.trans (hp.trans
    (congrArg₂ (fun (v w : (I.modules.obj ((monoidalCategory R).tensorObj M N)).val.obj W) ↦
      v + w) h₂' h₃'))

private theorem transportedPairing_smul_left
    (R : Sheaf J CommRingCat.{u}) (RI : Sheaf K CommRingCat.{u})
    (F : Sheaf J (Type u) ⥤ Sheaf K (Type u)) [F.Monoidal]
    (I : AlgebraicInverseImage F R RI)
    (M N : SheafOfModules.{u} (ringSheaf R)) (W : Dᵒᵖ)
    (a : RI.obj.obj W) (b : (I.modules.obj M).val.obj W)
    (c : (I.modules.obj N).val.obj W) :
    let β := imageBinary F (I.moduleUnderlying.app M) (I.moduleUnderlying.app N)
      (I.moduleUnderlying.app ((monoidalCategory R).tensorObj M N)) (pureSheaf R M N)
    β.hom.app W (a • b, c) =
      a • (show (I.modules.obj ((monoidalCategory R).tensorObj M N)).val.obj W from
        β.hom.app W (b, c)) := by
  let X := (sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R
  let Y := (underlying R).obj M
  let Z := (underlying R).obj N
  let P := (X ⊗ Y) ⊗ Z
  let x : P ⟶ X := CartesianMonoidalCategory.fst (X ⊗ Y) Z ≫
    CartesianMonoidalCategory.fst X Y
  let y : P ⟶ Y := CartesianMonoidalCategory.fst (X ⊗ Y) Z ≫
    CartesianMonoidalCategory.snd X Y
  let n : P ⟶ Z := CartesianMonoidalCategory.snd (X ⊗ Y) Z
  let s : P ⟶ Y := CartesianMonoidalCategory.lift x y ≫ GeometricConstruction.action R M
  let p : P ⟶ (underlying R).obj ((monoidalCategory R).tensorObj M N) :=
    CartesianMonoidalCategory.lift s n ≫ pureSheaf R M N
  let q : P ⟶ (underlying R).obj ((monoidalCategory R).tensorObj M N) :=
    CartesianMonoidalCategory.lift y n ≫ pureSheaf R M N
  obtain ⟨t, hx, hy, hn⟩ := tripleSections F I.ringUnderlying.symm
    (I.moduleUnderlying.app M) (I.moduleUnderlying.app N) W a b c
  have hs := I.moduleSMul M P x y s (fun _ _ ↦ rfl) W t
  change (F.map x ≫ I.ringUnderlying.hom).hom.app W t = a at hx
  change (F.map y ≫ I.moduleUnderlying.inv.app M).hom.app W t = b at hy
  change (F.map n ≫ I.moduleUnderlying.inv.app N).hom.app W t = c at hn
  have hs' := hs.trans (congrArg₂
    (fun (v : RI.obj.obj W) (w : (I.modules.obj M).val.obj W) ↦ v • w) hx hy)
  have hp := I.moduleSMul ((monoidalCategory R).tensorObj M N) P x q p
    (fun U v ↦ (pureBilin R M N U).map_smul₂ _ _ _) W t
  have h₁ := imageBinary_graph_apply F (I.moduleUnderlying.app M)
    (I.moduleUnderlying.app N) (I.moduleUnderlying.app ((monoidalCategory R).tensorObj M N))
    (pureSheaf R M N) s n W t
  have h₂ := imageBinary_graph_apply F (I.moduleUnderlying.app M)
    (I.moduleUnderlying.app N) (I.moduleUnderlying.app ((monoidalCategory R).tensorObj M N))
    (pureSheaf R M N) y n W t
  let β := imageBinary F (I.moduleUnderlying.app M) (I.moduleUnderlying.app N)
    (I.moduleUnderlying.app ((monoidalCategory R).tensorObj M N)) (pureSheaf R M N)
  let B (v : (I.modules.obj M).val.obj W) (w : (I.modules.obj N).val.obj W) :
      (I.modules.obj ((monoidalCategory R).tensorObj M N)).val.obj W := β.hom.app W (v, w)
  have h₁' := h₁.trans (congrArg₂ B hs' hn)
  have h₂' := h₂.trans (congrArg₂ B hy hn)
  exact h₁'.symm.trans (hp.trans (congrArg₂
    (fun (v : RI.obj.obj W)
      (w : (I.modules.obj ((monoidalCategory R).tensorObj M N)).val.obj W) ↦ v • w) hx h₂'))

private theorem transportedPairing_smul_right
    (R : Sheaf J CommRingCat.{u}) (RI : Sheaf K CommRingCat.{u})
    (F : Sheaf J (Type u) ⥤ Sheaf K (Type u)) [F.Monoidal]
    (I : AlgebraicInverseImage F R RI)
    (M N : SheafOfModules.{u} (ringSheaf R)) (W : Dᵒᵖ)
    (a : RI.obj.obj W) (b : (I.modules.obj N).val.obj W)
    (c : (I.modules.obj M).val.obj W) :
    let β := imageBinary F (I.moduleUnderlying.app M) (I.moduleUnderlying.app N)
      (I.moduleUnderlying.app ((monoidalCategory R).tensorObj M N)) (pureSheaf R M N)
    β.hom.app W (c, a • b) =
      a • (show (I.modules.obj ((monoidalCategory R).tensorObj M N)).val.obj W from
        β.hom.app W (c, b)) := by
  let X := (sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R
  let Y := (underlying R).obj N
  let Z := (underlying R).obj M
  let P := (X ⊗ Y) ⊗ Z
  let x : P ⟶ X := CartesianMonoidalCategory.fst (X ⊗ Y) Z ≫
    CartesianMonoidalCategory.fst X Y
  let y : P ⟶ Y := CartesianMonoidalCategory.fst (X ⊗ Y) Z ≫
    CartesianMonoidalCategory.snd X Y
  let n : P ⟶ Z := CartesianMonoidalCategory.snd (X ⊗ Y) Z
  let s : P ⟶ Y := CartesianMonoidalCategory.lift x y ≫ GeometricConstruction.action R N
  let p : P ⟶ (underlying R).obj ((monoidalCategory R).tensorObj M N) :=
    CartesianMonoidalCategory.lift n s ≫ pureSheaf R M N
  let q : P ⟶ (underlying R).obj ((monoidalCategory R).tensorObj M N) :=
    CartesianMonoidalCategory.lift n y ≫ pureSheaf R M N
  obtain ⟨t, hx, hy, hn⟩ := tripleSections F I.ringUnderlying.symm
    (I.moduleUnderlying.app N) (I.moduleUnderlying.app M) W a b c
  have hs := I.moduleSMul N P x y s (fun _ _ ↦ rfl) W t
  change (F.map x ≫ I.ringUnderlying.hom).hom.app W t = a at hx
  change (F.map y ≫ I.moduleUnderlying.inv.app N).hom.app W t = b at hy
  change (F.map n ≫ I.moduleUnderlying.inv.app M).hom.app W t = c at hn
  have hs' := hs.trans (congrArg₂
    (fun (v : RI.obj.obj W) (w : (I.modules.obj N).val.obj W) ↦ v • w) hx hy)
  have hp := I.moduleSMul ((monoidalCategory R).tensorObj M N) P x q p
    (fun U v ↦ (pureBilin R M N U _).map_smul _ _) W t
  have h₁ := imageBinary_graph_apply F (I.moduleUnderlying.app M)
    (I.moduleUnderlying.app N) (I.moduleUnderlying.app ((monoidalCategory R).tensorObj M N))
    (pureSheaf R M N) n s W t
  have h₂ := imageBinary_graph_apply F (I.moduleUnderlying.app M)
    (I.moduleUnderlying.app N) (I.moduleUnderlying.app ((monoidalCategory R).tensorObj M N))
    (pureSheaf R M N) n y W t
  let β := imageBinary F (I.moduleUnderlying.app M) (I.moduleUnderlying.app N)
    (I.moduleUnderlying.app ((monoidalCategory R).tensorObj M N)) (pureSheaf R M N)
  let B (v : (I.modules.obj M).val.obj W) (w : (I.modules.obj N).val.obj W) :
      (I.modules.obj ((monoidalCategory R).tensorObj M N)).val.obj W := β.hom.app W (v, w)
  have h₁' := h₁.trans (congrArg₂ B hn hs')
  have h₂' := h₂.trans (congrArg₂ B hn hy)
  exact h₁'.symm.trans (hp.trans (congrArg₂
    (fun (v : RI.obj.obj W)
      (w : (I.modules.obj ((monoidalCategory R).tensorObj M N)).val.obj W) ↦ v • w) hx h₂'))

/-- Transport of the actual pure pairing through the specified inverse-image lift.
Source: Stacks Project, Modules on Sites, Tag 03EL
(auxiliary; not a blueprint node). -/
noncomputable def inverseImagePurePairing
    (R : Sheaf J CommRingCat.{u}) (RI : Sheaf K CommRingCat.{u})
    (F : Sheaf J (Type u) ⥤ Sheaf K (Type u)) [PreservesFiniteLimits F]
    (I : AlgebraicInverseImage F R RI)
    (M N : SheafOfModules.{u} (ringSheaf R)) :
    (underlying RI).obj (I.modules.obj M) ⊗ (underlying RI).obj (I.modules.obj N) ⟶
      (underlying RI).obj (I.modules.obj ((monoidalCategory R).tensorObj M N)) := by
  let : F.Braided := Functor.Braided.ofChosenFiniteProducts F
  exact ((I.moduleUnderlying.hom.app M) ⊗ₘ (I.moduleUnderlying.hom.app N)) ≫
    Functor.LaxMonoidal.μ F _ _ ≫ F.map (pureSheaf R M N) ≫
      I.moduleUnderlying.inv.app ((monoidalCategory R).tensorObj M N)

/-- Naturality of the ordinary pure pairing.
Source: Stacks Project, Modules on Sites, Tag 03EL
(auxiliary; not a blueprint node). -/
theorem pureSheaf_natural (R : Sheaf J CommRingCat.{u})
    {M M' N N' : SheafOfModules.{u} (ringSheaf R)} (f : M ⟶ M') (g : N ⟶ N') :
    ((underlying R).map f ⊗ₘ (underlying R).map g) ≫ pureSheaf R M' N' =
      pureSheaf R M N ≫ (underlying R).map ((monoidalCategory R).tensorHom f g) := by
  ext W p
  exact (pure_map R f g W p.1 p.2).symm

/-- Naturality of the transported pure pairing.
Source: Stacks Project, Modules on Sites, Tag 03EL
(auxiliary; not a blueprint node). -/
theorem inverseImagePurePairing_natural
    (R : Sheaf J CommRingCat.{u}) (RI : Sheaf K CommRingCat.{u})
    (F : Sheaf J (Type u) ⥤ Sheaf K (Type u)) [PreservesFiniteLimits F]
    (I : AlgebraicInverseImage F R RI)
    {M M' N N' : SheafOfModules.{u} (ringSheaf R)} (f : M ⟶ M') (g : N ⟶ N') :
    ((underlying RI).map (I.modules.map f) ⊗ₘ (underlying RI).map (I.modules.map g)) ≫
        inverseImagePurePairing R RI F I M' N' =
      inverseImagePurePairing R RI F I M N ≫
        (underlying RI).map (I.modules.map ((monoidalCategory R).tensorHom f g)) := by
  let : F.Braided := Functor.Braided.ofChosenFiniteProducts F
  dsimp only [inverseImagePurePairing]
  rw [tensorHom_comp_tensorHom_assoc]
  have hf := I.moduleUnderlying.hom.naturality f
  have hg := I.moduleUnderlying.hom.naturality g
  change (underlying RI).map (I.modules.map f) ≫ I.moduleUnderlying.hom.app M' =
    I.moduleUnderlying.hom.app M ≫ F.map ((underlying R).map f) at hf
  change (underlying RI).map (I.modules.map g) ≫ I.moduleUnderlying.hom.app N' =
    I.moduleUnderlying.hom.app N ≫ F.map ((underlying R).map g) at hg
  rw [hf, hg, ← tensorHom_comp_tensorHom_assoc]
  rw [Functor.LaxMonoidal.μ_natural_assoc, ← F.map_comp_assoc, pureSheaf_natural,
    F.map_comp]
  simp only [Category.assoc]
  have ht := (I.moduleUnderlying.inv.naturality ((monoidalCategory R).tensorHom f g)).symm
  change I.moduleUnderlying.inv.app ((monoidalCategory R).tensorObj M N) ≫
      (underlying RI).map (I.modules.map ((monoidalCategory R).tensorHom f g)) =
    F.map ((underlying R).map ((monoidalCategory R).tensorHom f g)) ≫
      I.moduleUnderlying.inv.app ((monoidalCategory R).tensorObj M' N') at ht
  rw [ht]

/-- A canonical morphism from the tensor of inverse images to the inverse image of the
 tensor, with its normalization on every generalized pair.
Source: Stacks Project, Modules on Sites, Tag 03EL.
(auxiliary; not a blueprint node).

Proof: transport the ordinary pure pairing using the finite-product comparison and the
specified module-underlying isomorphisms. To check each additivity or scalar equation,
take the test sheaf of its three operands. Product preservation supplies a section above
any given target triple. Apply the graph axioms of the algebraic inverse image to the
source bilinear equation, and use the inverse-underlying isomorphisms on the projections.
The transported pairing commutes with restrictions since it is a sheaf morphism. The
sheaf tensor universal property supplies the required linear morphism. The product
comparison equation gives the displayed normalization for every test sheaf. -/
theorem exists_inverseImageTensorPairing
    (R : Sheaf J CommRingCat.{u}) (RI : Sheaf K CommRingCat.{u})
    (F : Sheaf J (Type u) ⥤ Sheaf K (Type u)) [PreservesFiniteLimits F]
    (I : AlgebraicInverseImage F R RI)
    (M N : SheafOfModules.{u} (ringSheaf R)) :
    ∃ b : (monoidalCategory RI).tensorObj (I.modules.obj M) (I.modules.obj N) ⟶
        I.modules.obj ((monoidalCategory R).tensorObj M N),
      (∀ W m n, b.val.app W (pure RI _ _ W m n) =
        (inverseImagePurePairing R RI F I M N).hom.app W (m, n)) ∧
      ∀ (Z : Sheaf J (Type u)) (x : Z ⟶ (underlying R).obj M)
        (y : Z ⟶ (underlying R).obj N)
        (z : Z ⟶ (underlying R).obj ((monoidalCategory R).tensorObj M N)),
        (∀ W t, z.hom.app W t = pure R M N W (x.hom.app W t) (y.hom.app W t)) →
        ∀ W t, b.val.app W
          (pure RI _ _ W ((F.map x ≫ I.moduleUnderlying.inv.app M).hom.app W t)
            ((F.map y ≫ I.moduleUnderlying.inv.app N).hom.app W t)) =
          (F.map z ≫ I.moduleUnderlying.inv.app
            ((monoidalCategory R).tensorObj M N)).hom.app W t := by
  let : F.Braided := Functor.Braided.ofChosenFiniteProducts F
  let B := imageBinary F (I.moduleUnderlying.app M) (I.moduleUnderlying.app N)
    (I.moduleUnderlying.app ((monoidalCategory R).tensorObj M N)) (pureSheaf R M N)
  let β (W : Dᵒᵖ) : (I.modules.obj M).val.obj W →ₗ[RI.obj.obj W]
      (I.modules.obj N).val.obj W →ₗ[RI.obj.obj W]
        (I.modules.obj ((monoidalCategory R).tensorObj M N)).val.obj W :=
    LinearMap.mk₂ _ (fun m n ↦ B.hom.app W (m, n))
      (fun m m' n ↦ transportedPairing_add_left R RI F I M N W m m' n)
      (fun r m n ↦ transportedPairing_smul_left R RI F I M N W r m n)
      (fun m n n' ↦ transportedPairing_add_right R RI F I M N W n n' m)
      (fun r m n ↦ transportedPairing_smul_right R RI F I M N W r n m)
  have hβ : ∀ {U V : Dᵒᵖ} (f : U ⟶ V) (m : (I.modules.obj M).val.obj U)
      (n : (I.modules.obj N).val.obj U),
      β V ((I.modules.obj M).val.map f m) ((I.modules.obj N).val.map f n) =
        (I.modules.obj ((monoidalCategory R).tensorObj M N)).val.map f (β U m n) := by
    intro U V f m n
    exact congrArg (fun k ↦ k (m, n)) (B.hom.naturality f)
  obtain ⟨b, hb, _⟩ := tensor_bilinear_universal RI (I.modules.obj M) (I.modules.obj N)
    (I.modules.obj ((monoidalCategory R).tensorObj M N)) β hβ
  refine ⟨b, hb, ?_⟩
  intro Z x y z hz W t
  have he : z = CartesianMonoidalCategory.lift x y ≫ pureSheaf R M N := by
    ext U v
    exact hz U v
  exact (hb W _ _).trans ((imageBinary_graph_apply F (I.moduleUnderlying.app M)
    (I.moduleUnderlying.app N) (I.moduleUnderlying.app ((monoidalCategory R).tensorObj M N))
    (pureSheaf R M N) x y W t).symm.trans
      (congrArg (fun k ↦ (F.map k ≫ I.moduleUnderlying.inv.app
        ((monoidalCategory R).tensorObj M N)).hom.app W t) he.symm))

end SheafOfModules.RingedTensor
