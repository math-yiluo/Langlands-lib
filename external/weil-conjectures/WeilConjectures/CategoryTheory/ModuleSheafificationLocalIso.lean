/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization

/-! # Locally specified isomorphisms after module sheafification

Source: Stacks Project, Tag 099E, identification after a covering refinement.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory Opposite
namespace PresheafOfModules
attribute [local instance] Classical.propDecidable
variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable {R : Sheaf J RingCat.{u}}
variable (M N : PresheafOfModules.{u} R.obj)
variable (E : Cᵒᵖ → Prop) (hE : ∀ {X Y : Cᵒᵖ}, (X ⟶ Y) → E X → E Y)

private def onLocus : M.Submodule where
  obj X := if E X then ⊤ else ⊥
  map {X Y} f := by
    intro x hx
    change M.map f x ∈ (if E Y then ⊤ else ⊥ : _root_.Submodule _ _)
    by_cases h : E X
    · rw [ite_eq_left (hE f h)]
      exact _root_.Submodule.mem_top
    · have hx0 : x = 0 := by
        change x ∈ (if E X then ⊤ else ⊥ : _root_.Submodule _ _) at hx
        simpa only [ite_eq_right h, _root_.Submodule.mem_bot] using hx
      rw [hx0, map_zero]
      exact _root_.Submodule.zero_mem _

private def locusMap
    (e : ∀ X, E X → M.obj X ≃ₗ[R.obj.obj X] N.obj X)
    (he : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) (h : E X) (x : M.obj X),
      e Y (hE f h) (M.map f x) = N.map f (e X h x)) :
    (onLocus M E hE).toPresheafOfModules ⟶ N where
  app X := ModuleCat.ofHom
    { toFun := fun x ↦ if h : E X then e X h x.1 else 0
      map_add' := by
        intro x y
        split_ifs with h <;> simp
      map_smul' := by
        intro r x
        split_ifs with h <;> simp }
  naturality {X Y} f := by
    ext x
    change (if h : E Y then e Y h (M.map f x.1) else 0) =
      N.map f (if h : E X then e X h x.1 else 0)
    by_cases h : E X
    · simp only [dite_eq_left h, dite_eq_left (hE f h)]
      exact he f h x.1
    · have hx : x.1 = 0 := by
        simpa only [onLocus, ite_eq_right h, _root_.Submodule.mem_bot] using x.2
      simp only [dite_eq_right h, hx, map_zero]
      split_ifs <;> simp

private theorem locusMap_injective
    (e : ∀ X, E X → M.obj X ≃ₗ[R.obj.obj X] N.obj X)
    (he : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) (h : E X) (x : M.obj X),
      e Y (hE f h) (M.map f x) = N.map f (e X h x)) (X : Cᵒᵖ) :
    Function.Injective ((locusMap M N E hE e he).app X) := by
  intro x y hxy
  apply Subtype.ext
  by_cases h : E X
  · apply (e X h).injective
    change (if h' : E X then e X h' x.1 else 0) =
      (if h' : E X then e X h' y.1 else 0) at hxy
    simpa only [dite_eq_left h] using hxy
  · have hx : x.1 = 0 := by
      simpa only [onLocus, ite_eq_right h, _root_.Submodule.mem_bot] using x.2
    have hy : y.1 = 0 := by
      simpa only [onLocus, ite_eq_right h, _root_.Submodule.mem_bot] using y.2
    exact hx.trans hy.symm

/-- Linear identifications on a restriction-stable locus which locally contains every
object induce an isomorphism after sheafification.
Source: Stacks Project, Tag 099E, local identities glue after sheafification.
(auxiliary; not a blueprint node).

Proof: take the subpresheaf of M which equals M on the locus and is zero elsewhere.
It maps injectively to M and to N, using the prescribed local linear equivalences.
Both maps are locally surjective because the locus covers every object. They become
isomorphisms under sheafification; compose the inverse of the first with the second. -/
theorem exists_sheafificationIso_of_localEquiv
    (hcover : ∀ X : C, ∃ S ∈ J X, ∀ (Y : C) (f : Y ⟶ X), S f → E (op Y))
    (e : ∀ X, E X → M.obj X ≃ₗ[R.obj.obj X] N.obj X)
    (he : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) (h : E X) (x : M.obj X),
      e Y (hE f h) (M.map f x) = N.map f (e X h x)) :
    ∃ z : (sheafification (𝟙 R.obj)).obj M ≅
        (sheafification (𝟙 R.obj)).obj N,
      ∀ (X : Cᵒᵖ) (h : E X) (x : M.obj X),
        z.hom.val.app X (((sheafificationAdjunction (𝟙 R.obj)).unit.app M).app X x) =
          (((sheafificationAdjunction (𝟙 R.obj)).unit.app N).app X (e X h x)) := by
  let P := onLocus M E hE
  let a := P.ι
  let b := locusMap M N E hE e he
  have haI : Presheaf.IsLocallyInjective J ((toPresheaf R.obj).map a) :=
    Presheaf.isLocallyInjective_of_injective J _ (fun X ↦ Subtype.val_injective)
  have hbI : Presheaf.IsLocallyInjective J ((toPresheaf R.obj).map b) :=
    Presheaf.isLocallyInjective_of_injective J _ (locusMap_injective M N E hE e he)
  have haS : Presheaf.IsLocallySurjective J ((toPresheaf R.obj).map a) := by
    constructor
    intro X x
    obtain ⟨S, hS, h⟩ := hcover X
    apply J.superset_covering _ hS
    intro Y f hf
    refine ⟨⟨M.map f.op x, ?_⟩, rfl⟩
    change M.map f.op x ∈ (if E (op Y) then ⊤ else ⊥ : _root_.Submodule _ _)
    rw [ite_eq_left (h Y f hf)]
    exact _root_.Submodule.mem_top
  have hbS : Presheaf.IsLocallySurjective J ((toPresheaf R.obj).map b) := by
    constructor
    intro X x
    obtain ⟨S, hS, h⟩ := hcover X
    apply J.superset_covering _ hS
    intro Y f hf
    let y := (e (op Y) (h Y f hf)).symm (N.map f.op x)
    refine ⟨⟨y, ?_⟩, ?_⟩
    · change y ∈ (if E (op Y) then ⊤ else ⊥ : _root_.Submodule _ _)
      rw [ite_eq_left (h Y f hf)]
      exact _root_.Submodule.mem_top
    · change (if h' : E (op Y) then e (op Y) h' y else 0) = N.map f.op x
      simp only [dite_eq_left (h Y f hf), y, LinearEquiv.apply_symm_apply]
  have haW := J.W_of_isLocallyBijective ((toPresheaf R.obj).map a)
  have hbW := J.W_of_isLocallyBijective ((toPresheaf R.obj).map b)
  have haIso : IsIso ((sheafification (𝟙 R.obj)).map a) := by
    change ((CategoryTheory.MorphismProperty.isomorphisms _).inverseImage
      (sheafification (𝟙 R.obj))) a
    rw [← inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms]
    exact haW
  have hbIso : IsIso ((sheafification (𝟙 R.obj)).map b) := by
    change ((CategoryTheory.MorphismProperty.isomorphisms _).inverseImage
      (sheafification (𝟙 R.obj))) b
    rw [← inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms]
    exact hbW
  let S := sheafification (𝟙 R.obj)
  let z := (asIso (S.map a)).symm ≪≫ asIso (S.map b)
  refine ⟨z, ?_⟩
  intro X h x
  let y : P.toPresheafOfModules.obj X := ⟨x, by
    change x ∈ (if E X then ⊤ else ⊥ : _root_.Submodule _ _)
    rw [ite_eq_left h]
    exact _root_.Submodule.mem_top⟩
  let η := (sheafificationAdjunction (𝟙 R.obj)).unit
  have hA := congrArg (fun k ↦ k.app X y) (η.naturality a)
  have hB := congrArg (fun k ↦ k.app X y) (η.naturality b)
  change (η.app M).app X x = (S.map a).val.app X ((η.app P.toPresheafOfModules).app X y)
    at hA
  change (η.app N).app X (if h' : E X then e X h' x else 0) =
    (S.map b).val.app X ((η.app P.toPresheafOfModules).app X y) at hB
  simp only [dite_eq_left h] at hB
  have hz : S.map a ≫ z.hom = S.map b := by
    simp only [z, Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv,
      IsIso.hom_inv_id_assoc]
  have hzX := congrArg
    (fun k ↦ k.val.app X ((η.app P.toPresheafOfModules).app X y)) hz
  change z.hom.val.app X ((S.map a).val.app X
      ((η.app P.toPresheafOfModules).app X y)) =
    (S.map b).val.app X ((η.app P.toPresheafOfModules).app X y) at hzX
  change z.hom.val.app X ((η.app M).app X x) = (η.app N).app X (e X h x)
  rw [hA]
  exact hzX.trans hB.symm

/-- Maps out of a sheafification are determined by presheaf sections on a covering locus.
Source: Stacks Project, Tag 099E, uniqueness of the local identification.
(auxiliary; not a blueprint node).
Proof: use the sheafification adjunction, then separatedness on the given covering sieves. -/
theorem sheafification_hom_ext_on_locus
    (hcover : ∀ X : C, ∃ S ∈ J X, ∀ (Y : C) (f : Y ⟶ X), S f → E (op Y))
    (L : SheafOfModules.{u} R)
    (f g : (sheafification (𝟙 R.obj)).obj M ⟶ L)
    (h : ∀ (X : Cᵒᵖ), E X → ∀ x : M.obj X,
      f.val.app X (((sheafificationAdjunction (𝟙 R.obj)).unit.app M).app X x) =
        g.val.app X (((sheafificationAdjunction (𝟙 R.obj)).unit.app M).app X x)) :
    f = g := by
  let adj := sheafificationAdjunction (𝟙 R.obj)
  apply (adj.homEquiv M L).injective
  let f' := adj.homEquiv M L f
  let g' := adj.homEquiv M L g
  apply PresheafOfModules.hom_ext
  intro X
  ext x
  obtain ⟨S, hS, hE'⟩ := hcover X.unop
  have hL : Presieve.IsSheaf J (L.val.presheaf ⋙ forget AddCommGrpCat.{u}) :=
    (isSheaf_iff_isSheaf_of_type _ _).1
      (Presheaf.isSheaf_comp_of_isSheaf J L.val.presheaf
        (forget AddCommGrpCat.{u}) L.isSheaf)
  apply (hL S hS).isSeparatedFor.ext
  intro Y a ha
  change L.val.map a.op (f'.app X x) = L.val.map a.op (g'.app X x)
  have hf := PresheafOfModules.naturality_apply f' a.op x
  have hg := PresheafOfModules.naturality_apply g' a.op x
  change f'.app (op Y) (M.map a.op x) = L.val.map a.op (f'.app X x) at hf
  change g'.app (op Y) (M.map a.op x) = L.val.map a.op (g'.app X x) at hg
  exact hf.symm.trans ((h (op Y) (hE' Y a ha) (M.map a.op x)).trans hg)

/-- Module sheafification is additive, as an additive left adjoint.
Source: the sheafification adjunction.
(auxiliary; not a blueprint node). -/
instance moduleSheafification_additive (R : Sheaf J RingCat.{u}) :
    (sheafification (𝟙 R.obj)).Additive :=
  (sheafificationAdjunction (𝟙 R.obj)).left_adjoint_additive

/-- Compatible linear identifications on a covering locus give an augmentation-compatible
isomorphism of the degreewise sheafified complexes.
Source: Stacks Project, Tag 099E, the local identities of augmented complexes.
(auxiliary; not a blueprint node).

Proof: obtain the degreewise isomorphisms from the local-equivalence theorem. Their
commutation with differentials follows by testing the two maps on presheaf sections on
the locus, where it is the stated differential equation. The same uniqueness test proves
the augmentation square. -/
theorem exists_augmentedSheafificationIso_of_localEquiv_with_unit
    (M N : CochainComplex (PresheafOfModules.{u} R.obj) ℤ)
    (B : CochainComplex (SheafOfModules.{u} R) ℤ)
    (a : ((sheafification (𝟙 R.obj)).mapHomologicalComplex (.up ℤ)).obj M ⟶ B)
    (b : ((sheafification (𝟙 R.obj)).mapHomologicalComplex (.up ℤ)).obj N ⟶ B)
    (hcover : ∀ X : C, ∃ S ∈ J X, ∀ (Y : C) (f : Y ⟶ X), S f → E (op Y))
    (e : ∀ (n : ℤ) (X : Cᵒᵖ), E X → (M.X n).obj X ≃ₗ[R.obj.obj X] (N.X n).obj X)
    (he : ∀ (n : ℤ) {X Y : Cᵒᵖ} (f : X ⟶ Y) (h : E X) (x : (M.X n).obj X),
      e n Y (hE f h) ((M.X n).map f x) = (N.X n).map f (e n X h x))
    (hd : ∀ (n k : ℤ) (X : Cᵒᵖ) (h : E X) (x : (M.X n).obj X),
      e k X h ((M.d n k).app X x) = (N.d n k).app X (e n X h x))
    (ha : ∀ (n : ℤ) (X : Cᵒᵖ) (h : E X) (x : (M.X n).obj X),
      (b.f n).val.app X
          (((sheafificationAdjunction (𝟙 R.obj)).unit.app (N.X n)).app X (e n X h x)) =
        (a.f n).val.app X
          (((sheafificationAdjunction (𝟙 R.obj)).unit.app (M.X n)).app X x)) :
    ∃ z : ((sheafification (𝟙 R.obj)).mapHomologicalComplex (.up ℤ)).obj M ≅
        ((sheafification (𝟙 R.obj)).mapHomologicalComplex (.up ℤ)).obj N,
      z.hom ≫ b = a ∧
        ∀ (n : ℤ) (X : Cᵒᵖ) (h : E X) (x : (M.X n).obj X),
          (z.hom.f n).val.app X
              (((sheafificationAdjunction (𝟙 R.obj)).unit.app (M.X n)).app X x) =
            (((sheafificationAdjunction (𝟙 R.obj)).unit.app (N.X n)).app X (e n X h x)) := by
  let S := sheafification (𝟙 R.obj)
  let η := (sheafificationAdjunction (𝟙 R.obj)).unit
  choose z hz using fun n ↦ exists_sheafificationIso_of_localEquiv
    (M.X n) (N.X n) E hE hcover (e n) (he n)
  have hd' (n k : ℤ) :
      (z n).hom ≫ S.map (N.d n k) = S.map (M.d n k) ≫ (z k).hom := by
    apply sheafification_hom_ext_on_locus (M.X n) E hcover
    intro X h x
    change (S.map (N.d n k)).val.app X
        ((z n).hom.val.app X ((η.app (M.X n)).app X x)) =
      (z k).hom.val.app X
        ((S.map (M.d n k)).val.app X ((η.app (M.X n)).app X x))
    rw [hz n X h x]
    have hM := congrArg (fun t ↦ t.app X x) (η.naturality (M.d n k))
    have hN := congrArg (fun t ↦ t.app X (e n X h x)) (η.naturality (N.d n k))
    change (η.app (M.X k)).app X ((M.d n k).app X x) =
      (S.map (M.d n k)).val.app X ((η.app (M.X n)).app X x) at hM
    change (η.app (N.X k)).app X ((N.d n k).app X (e n X h x)) =
      (S.map (N.d n k)).val.app X ((η.app (N.X n)).app X (e n X h x)) at hN
    rw [← hM, hz k X h, hd, ← hN]
  let z' : (S.mapHomologicalComplex (.up ℤ)).obj M ≅
      (S.mapHomologicalComplex (.up ℤ)).obj N :=
    HomologicalComplex.Hom.isoOfComponents z (fun n k _ ↦ hd' n k)
  refine ⟨z', ?_, ?_⟩
  · apply HomologicalComplex.hom_ext
    intro n
    apply sheafification_hom_ext_on_locus (M.X n) E hcover
    intro X h x
    change (b.f n).val.app X ((z n).hom.val.app X ((η.app (M.X n)).app X x)) =
      (a.f n).val.app X ((η.app (M.X n)).app X x)
    rw [hz n X h x]
    exact ha n X h x
  · intro n X h x
    exact hz n X h x

end PresheafOfModules
