/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.Sites.PresheafCechComplex
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.AlgebraicTopology.ExtraDegeneracy
import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact

/-! # Positive exactness of the sheafified free presheaf Čech nerve

Source: Stacks Project, Tag 01GC.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Sheaf

set_option backward.isDefEq.respectTransparency false in
private noncomputable def nerveMonoIso
    {D : Type u} [Category.{v} D] [HasFiniteLimits D]
    (f : Arrow D) {Z : D} (g : f.right ⟶ Z) [Mono g] :
    f.cechNerve ≅ (Arrow.mk (f.hom ≫ g)).cechNerve := by
  let h := f.hom ≫ g
  refine NatIso.ofComponents (fun n ↦ ?_) ?_
  · refine
      { hom := WidePullback.lift
          (WidePullback.base (fun _ : Fin (n.unop.len + 1) ↦ f.hom) ≫ g)
          (fun j ↦ WidePullback.π (fun _ : Fin (n.unop.len + 1) ↦ f.hom) j)
          (by intro j; simp)
        inv := WidePullback.lift
          (WidePullback.π (fun _ : Fin (n.unop.len + 1) ↦ h) 0 ≫ f.hom)
          (fun j ↦ WidePullback.π (fun _ : Fin (n.unop.len + 1) ↦ h) j)
          (by intro j; apply (cancel_mono g).1; simp [h, Category.assoc])
        hom_inv_id := ?_
        inv_hom_id := ?_ }
    · apply WidePullback.hom_ext
      · intro j; simp [h, Category.assoc]
      · simp [h, Category.assoc]
    · apply WidePullback.hom_ext <;> simp [Category.assoc, h]
  · intro n m α
    apply WidePullback.hom_ext <;> simp [Arrow.cechNerve, Category.assoc]


private theorem type_nerve_positive_exact (f : Arrow (Type v)) (n : ℕ) :
    ((AlgebraicTopology.alternatingFaceMapComplex _).obj
      (f.cechNerve ⋙ AddCommGrpCat.free)).ExactAt (n + 1) := by
  classical
  let I : Type v := Set.range f.hom
  let p : f.left ⟶ I := ↾fun a ↦ ⟨f.hom a, ⟨a, rfl⟩⟩
  let j : I ⟶ f.right := ↾fun b ↦ b.1
  have hj : Mono j := (mono_iff_injective _).2 Subtype.val_injective
  have hp : Function.Surjective p := by
    rintro ⟨b, a, rfl⟩
    exact ⟨a, rfl⟩
  obtain ⟨s, hs⟩ := hp.hasRightInverse
  let S : SplitEpi p := { section_ := ↾s, id := by ext b; exact congrArg Subtype.val (hs b) }
  let ed := (Arrow.AugmentedCechNerve.extraDegeneracy (Arrow.mk p) S).map
    AddCommGrpCat.free
  let he := ed.homotopyEquiv
  have hsingle : ((ChainComplex.single₀ AddCommGrpCat).obj
      (AddCommGrpCat.free.obj I)).ExactAt (n + 1) := by
    apply HomologicalComplex.ExactAt.of_isZero
    exact HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)
  have hx : ((AlgebraicTopology.alternatingFaceMapComplex _).obj
      ((Arrow.mk p).cechNerve ⋙ AddCommGrpCat.free)).ExactAt (n + 1) := by
    apply (HomologicalComplex.exactAt_iff_isZero_homology _ _).2
    exact (he.toHomologyIso (n + 1)).isZero_iff.2
      ((HomologicalComplex.exactAt_iff_isZero_homology _ _).1 hsingle)
  let e := nerveMonoIso (Arrow.mk p) j
  have hfac : p ≫ j = f.hom := by ext a; rfl
  have hf : Arrow.mk (p ≫ j) = f := by cases f; simp_all
  change (Arrow.mk p).cechNerve ≅ (Arrow.mk (p ≫ j)).cechNerve at e
  rw [hf] at e
  exact hx.of_iso
    ((AlgebraicTopology.alternatingFaceMapComplex _).mapIso
      ((SimplicialObject.whiskering _ _).obj AddCommGrpCat.free |>.mapIso e))

set_option backward.isDefEq.respectTransparency false in
private noncomputable def nerveMapIso
    {D E : Type*} [Category D] [Category E] [HasFiniteLimits D] [HasFiniteLimits E]
    (F : D ⥤ E) [PreservesFiniteLimits F] (f : Arrow D) :
    f.cechNerve ⋙ F ≅ (Arrow.mk (F.map f.hom)).cechNerve := by
  let L (n : SimplexCategoryᵒᵖ) :=
    WidePullbackShape.wideCospan f.right (fun _ : Fin (n.unop.len + 1) ↦ f.left)
      (fun _ ↦ f.hom)
  let R (n : SimplexCategoryᵒᵖ) :=
    WidePullbackShape.wideCospan (F.obj f.right)
      (fun _ : Fin (n.unop.len + 1) ↦ F.obj f.left) (fun _ ↦ F.map f.hom)
  let eD (n : SimplexCategoryᵒᵖ) : L n ⋙ F ≅ R n :=
    NatIso.ofComponents (fun j ↦ match j with
      | none => Iso.refl _
      | some _ => Iso.refl _)
      (by intro j k α; cases α with
          | id j =>
              change F.map ((L n).map (𝟙 j)) ≫ _ = _ ≫ (R n).map (𝟙 j)
              rw [(L n).map_id, (R n).map_id, F.map_id]
              simp
          | term j => simp [L, R])
  let e (n : SimplexCategoryᵒᵖ) : F.obj (limit (L n)) ≅ limit (R n) :=
    preservesLimitIso F (L n) ≪≫ HasLimit.isoOfNatIso (eD n)
  have hπ (n : SimplexCategoryᵒᵖ) (j : Fin (n.unop.len + 1)) :
      (e n).hom ≫ WidePullback.π (fun _ ↦ F.map f.hom) j =
        F.map (WidePullback.π (fun _ ↦ f.hom) j) := by
    change (e n).hom ≫ limit.π (R n) (some j) = F.map (limit.π (L n) (some j))
    dsimp only [e, Iso.trans_hom]
    rw [Category.assoc, HasLimit.isoOfNatIso_hom_π, ← Category.assoc,
      preservesLimitIso_hom_π]
    simp [eD]
  have hb (n : SimplexCategoryᵒᵖ) :
      (e n).hom ≫ WidePullback.base (fun _ : Fin (n.unop.len + 1) ↦ F.map f.hom) =
        F.map (WidePullback.base (fun _ : Fin (n.unop.len + 1) ↦ f.hom)) := by
    change (e n).hom ≫ limit.π (R n) none = F.map (limit.π (L n) none)
    dsimp only [e, Iso.trans_hom]
    rw [Category.assoc, HasLimit.isoOfNatIso_hom_π, ← Category.assoc,
      preservesLimitIso_hom_π]
    simp [eD]
  refine NatIso.ofComponents e ?_
  intro n m α
  apply WidePullback.hom_ext
  · intro j
    dsimp only [Arrow.mk, Functor.comp_map]
    rw [Category.assoc, hπ]
    simp only [← F.map_comp]
    simp [Arrow.cechNerve, Category.assoc, hπ]
  · dsimp only [Arrow.mk, Functor.comp_map]
    rw [Category.assoc, hb]
    simp only [← F.map_comp]
    simp [Arrow.cechNerve, Category.assoc, hb]

private theorem presheaf_nerve_positive_exact
    {C : Type u} [Category.{v} C] (f : Arrow (Cᵒᵖ ⥤ Type v)) (n : ℕ) :
    ((AlgebraicTopology.alternatingFaceMapComplex _).obj
      (f.cechNerve ⋙ (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free)).ExactAt
        (n + 1) := by
  let P := (AlgebraicTopology.alternatingFaceMapComplex _).obj
    (f.cechNerve ⋙ (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free)
  let E := fun X ↦ (evaluation Cᵒᵖ AddCommGrpCat.{v}).obj X
  have hjoint : JointlyFaithful E := ⟨by
    intro P Q α β h
    apply NatTrans.ext
    funext X
    exact h X⟩
  apply hjoint.jointlyReflectsIsomorphisms.exact_iff _ |>.2
  intro X
  let V := (evaluation Cᵒᵖ (Type v)).obj X
  let q := Arrow.mk (f.hom.app X)
  let eN := nerveMapIso V f
  let eFree := (SimplicialObject.whiskering _ _).obj AddCommGrpCat.free |>.mapIso eN
  let eP := (AlgebraicTopology.alternatingFaceMapComplex _).mapIso eFree
  have h := type_nerve_positive_exact q n
  have h' := h.of_iso eP.symm
  change (((AlgebraicTopology.alternatingFaceMapComplex _) ⋙
    (E X).mapHomologicalComplex _).obj
    (f.cechNerve ⋙ (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free)).ExactAt
      (n + 1)
  rw [AlgebraicTopology.map_alternatingFaceMapComplex]
  exact h'

/-- The sheafified free Čech chain complex is exact in every positive degree.
Source: Stacks Project, Tag 01GC, positive-degree part.
(blueprint: lem-sc-presheaf-cech-sheaf-positive-exact)

Proof: replacing a set map's target by its image leaves its nerve unchanged;
`nerveMonoIso` constructs the isomorphism by the wide-pullback universal property.
The map onto the image has a section by choice, so Mathlib's extra degeneracy,
linearization, and homotopy equivalence identify its free nerve with the free
abelian group on the image in degree zero. Therefore positive homology vanishes.
The finite-limit comparison `nerveMapIso` identifies evaluation of the presheaf
nerve with the nerve of the evaluated map. Evaluation commutes with free abelian
groups and alternating faces, and the jointly faithful evaluation functors detect
exactness. Finally exact, additive sheafification preserves this exactness and
commutes with the alternating-face construction. Empty sources give zero terms.
-/
theorem presheafCechSheaf_positive_exact
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{v}] (f : Arrow (Cᵒᵖ ⥤ Type v)) :
  let F := (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙
    presheafToSheaf J AddCommGrpCat
  let A := (AlgebraicTopology.alternatingFaceMapComplex _).obj (f.cechNerve ⋙ F)
  ∀ n : ℕ, A.ExactAt (n + 1) := by
  dsimp only
  intro n
  let P := (AlgebraicTopology.alternatingFaceMapComplex _).obj
    (f.cechNerve ⋙ (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free)
  let F := presheafToSheaf J AddCommGrpCat.{v}
  have hpre : P.ExactAt (n + 1) := presheaf_nerve_positive_exact f n
  have hmap := hpre.map F
  change (((AlgebraicTopology.alternatingFaceMapComplex _) ⋙
    F.mapHomologicalComplex _).obj
    (f.cechNerve ⋙ (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free)).ExactAt
      (n + 1) at hmap
  rw [AlgebraicTopology.map_alternatingFaceMapComplex] at hmap
  exact hmap

end CategoryTheory.Sheaf
