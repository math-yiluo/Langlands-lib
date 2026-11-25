/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Limits.Types.Colimits
import Mathlib.CategoryTheory.Limits.Types.Filtered

/-!
# One-cover refinement of a pointed inverse system

Source: Stacks Project, Sites, Tag 00YO (Lemma lemma-refine), proof of Tag 00YP
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u v w t r

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

set_option autoImplicit false

private def RefineIndex (J : Type w) [Preorder J] (j₀ : J) :=
  J ⊕ {j : J // j₀ ≤ j}

private instance {J : Type w} [Preorder J] (j₀ : J) : Preorder (RefineIndex J j₀) where
  le x y := match x, y with
    | .inl i, .inl j => i ≤ j
    | .inl i, .inr j => i ≤ j.val
    | .inr _, .inl _ => False
    | .inr i, .inr j => i.val ≤ j.val
  le_refl x := by cases x <;> exact le_rfl
  le_trans x y z hxy hyz := by
    cases x <;> cases y <;> cases z <;>
      first | exact hxy.elim | exact hyz.elim | exact le_trans hxy hyz

private instance {J : Type w} [Preorder J] [Nonempty J] (j₀ : J) :
    Nonempty (RefineIndex J j₀) := ⟨Sum.inl j₀⟩

private instance {J : Type w} [Preorder J] [IsDirected J (· ≤ ·)] (j₀ : J) :
    IsDirected (RefineIndex J j₀) (· ≤ ·) where
  directed x y := by
    have upper (i j : J) : ∃ k, i ≤ k ∧ j ≤ k ∧ j₀ ≤ k := by
      obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
      obtain ⟨l, hkl, h₀l⟩ := directed_of (· ≤ ·) k j₀
      exact ⟨l, hik.trans hkl, hjk.trans hkl, h₀l⟩
    cases x with
    | inl x =>
      cases y with
      | inl y =>
        obtain ⟨k, hx, hy, h₀⟩ := upper x y
        exact ⟨Sum.inr ⟨k, h₀⟩, hx, hy⟩
      | inr y =>
        obtain ⟨k, hx, hy, h₀⟩ := upper x y.val
        exact ⟨Sum.inr ⟨k, h₀⟩, hx, hy⟩
    | inr x =>
      cases y with
      | inl y =>
        obtain ⟨k, hx, hy, h₀⟩ := upper x.val y
        exact ⟨Sum.inr ⟨k, h₀⟩, hx, hy⟩
      | inr y =>
        obtain ⟨k, hx, hy, h₀⟩ := upper x.val y.val
        exact ⟨Sum.inr ⟨k, h₀⟩, hx, hy⟩

private def refineInclusion {J : Type w} [Preorder J] (j₀ : J) :
    J ↪o RefineIndex J j₀ where
  toFun := Sum.inl
  inj' := Sum.inl_injective
  map_rel_iff' := Iff.rfl

private def tailInclusion {J : Type w} [Preorder J] (j₀ : J) :
    {j : J // j₀ ≤ j} ⥤ J :=
  (show Monotone (fun j : {j : J // j₀ ≤ j} ↦ j.val) from fun _ _ h ↦ h).functor

private def refineDiagram {C : Type u} [Category.{v} C]
    {J : Type w} [Preorder J] (j₀ : J) (D : J ⥤ C)
    (B : {j : J // j₀ ≤ j} ⥤ C) (α : tailInclusion j₀ ⋙ D ⟶ B) :
    RefineIndex J j₀ ⥤ C where
  obj x := match x with
    | .inl j => D.obj j
    | .inr j => B.obj j
  map {x y} f := match x, y with
    | .inl _, .inl _ => D.map (homOfLE (leOfHom f))
    | .inl _, .inr j => D.map (homOfLE (leOfHom f)) ≫ α.app j
    | .inr _, .inl _ => (leOfHom f).elim
    | .inr _, .inr _ => B.map (homOfLE (leOfHom f))
  map_id x := by cases x <;> simp
  map_comp {x y z} f g := by
    cases x <;> cases y <;> cases z
    all_goals first
      | exact (leOfHom f).elim
      | exact (leOfHom g).elim
      | simp only [← Functor.map_comp, homOfLE_comp]
    all_goals try rw [Category.assoc, ← α.naturality]
    all_goals simp only [← Category.assoc, ← Functor.map_comp]
    all_goals congr 2
    change D.map _ = D.map _ ≫ D.map _
    rw [← D.map_comp]
    congr 1

private theorem refineDiagram_restrict {C : Type u} [Category.{v} C]
    {J : Type w} [Preorder J] (j₀ : J) (D : J ⥤ C)
    (B : {j : J // j₀ ≤ j} ⥤ C) (α : tailInclusion j₀ ⋙ D ⟶ B) :
    (refineInclusion j₀).toOrderHom.toFunctor ⋙ refineDiagram j₀ D B α = D := by
  apply Functor.ext (fun _ ↦ rfl)

private theorem finite_persistent_ne
    {L : Type w} [Preorder L] [IsFiltered L]
    {A : Type r} [Finite A] (G : L ⥤ Type t) (H : A → L ⥤ Type t)
    (α : ∀ k, G ⟶ H k)
    (hinj : ∀ j (x y : G.obj j), (∀ k, (α k).app j x = (α k).app j y) → x = y)
    (j₀ : L) (x y : G.obj j₀)
    (hne : ∀ j (f : j₀ ⟶ j), G.map f x ≠ G.map f y) :
    ∃ k, ∀ j (f : j₀ ⟶ j),
      (α k).app j (G.map f x) ≠ (α k).app j (G.map f y) := by
  classical
  by_contra h
  push Not at h
  choose j f he using h
  obtain ⟨l, a, b, hab⟩ := IsFiltered.wideSpan f
  apply hne l a
  apply hinj l
  intro k
  have h := congrArg (fun z ↦ (H k).map (b k) z) (he k)
  have hx := ConcreteCategory.congr_hom ((α k).naturality (b k)) (G.map (f k) x)
  have hy := ConcreteCategory.congr_hom ((α k).naturality (b k)) (G.map (f k) y)
  simp only [types_comp_apply] at hx hy
  simp only [← G.map_comp_apply, hab] at hx hy
  exact hx.trans (h.trans hy.symm)

private noncomputable def pullbackDiagram
    {C : Type u} [Category.{v} C] {L : Type w} [Preorder L]
    (D : Lᵒᵖ ⥤ C) {W Z : C} (a : Z ⟶ W)
    (b : ∀ j, D.obj (Opposite.op j) ⟶ W)
    (hb : ∀ {i j} (f : i ⟶ j), D.map f.op ≫ b i = b j)
    (Q : L → C) (p : ∀ j, Q j ⟶ D.obj (Opposite.op j))
    (q : ∀ j, Q j ⟶ Z) (hp : ∀ j, IsPullback (p j) (q j) (b j) a) :
    L ⥤ Cᵒᵖ where
  obj j := Opposite.op (Q j)
  map {i j} f := ((hp i).lift (p j ≫ D.map f.op) (q j) (by
    rw [Category.assoc, hb, (hp j).w])).op
  map_id i := by
    apply Quiver.Hom.unop_inj
    apply (hp i).hom_ext <;> simp
  map_comp {i j k} f g := by
    apply Quiver.Hom.unop_inj
    apply (hp i).hom_ext <;> simp [← Functor.map_comp]

private noncomputable def pullbackTransformation
    {C : Type u} [Category.{v} C] {L : Type w} [Preorder L]
    (D : Lᵒᵖ ⥤ C) {W Z : C} (a : Z ⟶ W)
    (b : ∀ j, D.obj (Opposite.op j) ⟶ W)
    (hb : ∀ {i j} (f : i ⟶ j), D.map f.op ≫ b i = b j)
    (Q : L → C) (p : ∀ j, Q j ⟶ D.obj (Opposite.op j))
    (q : ∀ j, Q j ⟶ Z) (hp : ∀ j, IsPullback (p j) (q j) (b j) a) :
    D.rightOp ⟶ pullbackDiagram D a b hb Q p q hp where
  app j := (p j).op
  naturality i j f := by
    apply Quiver.Hom.unop_inj
    simp [pullbackDiagram]

private theorem refinementMap_ι
    {C : Type u} [Category.{v} C] {J I : Type w} [Preorder J] [Preorder I]
    (D : J ⥤ C) (R : I ⥤ C) (e : J ↪o I)
    (h : e.toOrderHom.toFunctor ⋙ R = D) (H : C ⥤ Type (max w t)) (j : J) :
    colimit.ι (D ⋙ H) j ≫
        eqToHom (congrArg (fun X : J ⥤ C ↦ colimit (X ⋙ H)) h).symm ≫
        colimit.pre (R ⋙ H) e.toOrderHom.toFunctor =
      H.map (eqToHom (congrArg (fun X : J ⥤ C ↦ X.obj j) h).symm) ≫
        colimit.ι (R ⋙ H) (e j) := by
  cases h
  simp only [Functor.assoc, eqToHom_refl, Functor.map_id,
    Category.id_comp]
  convert colimit.ι_pre (R ⋙ H) e.toOrderHom.toFunctor j using 1
  rfl

/-- The one-cover refinement lemma for the inverse-system point construction.

The section stalk is the filtered colimit of `F` along `V`, and the functor `u'`
is the filtered colimit of universe-lifted Yoneda representables along the same
inverse system. The index types live in an arbitrary universe `w`, the sheaf
takes values in `Type (max w t)` and the representables are lifted to
`Type (max w v)`, so that the filtered colimits over `J` exist without tying
`J`, `K` or the sheaf to the object universe of `C`. The canonical maps to a
refinement are Mathlib's `colimit.pre`; the factorization clause uses the map
induced by `uliftYoneda.map (wk k)`.

Proof steps from Tag 00YO:
1. Represent `f` at an index of `J`, pass to its directed tail, and pull back the
   finite covering along that representative using the site pullback axiom
   [def-weil-pbc-sites-and-cohomology].
2. Apply the sheaf equalizer to obtain an injection into the finite product of
   sections on the pullbacks, and use filtered-colimit commutation with finite
   limits [lem-weil-pbc-filtered-colimits-commute-finite-limits] to choose a
   cover member preserving the distinct images of `s` and `s'`.
3. Form the disjoint-union refinement of the original index poset and its tail,
   with the pullback objects and transition maps from the proof of Tag 00YO.
4. The tail copy is cofinal, so distinctness survives under `colimit.pre`, and
   the pullback square gives the required factorization through `W_k`.
The equality `h` is retained explicitly so that both canonical maps remain
well-typed for arbitrary index and sheaf universes.

Source: Stacks Project, Sites, Tag 00YO (Lemma lemma-refine), proof of Tag 00YP
(auxiliary; not a blueprint node).
-/
theorem pointSystemRefine
    {C : Type u} [Category.{v} C]
    (P : Precoverage C) (hP : P.IsSiteForCoverings)
    {J : Type w} [Preorder J] [Nonempty J] [IsDirected J (· ≤ ·)]
    (V : Jᵒᵖ ⥤ C)
    (F : Sheaf P.toGrothendieck (Type (max w t)))
    {K : Type r} [Finite K]
    {W : C} (Wk : K → C) (wk : ∀ k, Wk k ⟶ W)
    (hcover : Presieve.ofArrows Wk wk ∈ P W)
    (s s' : colimit (V.rightOp ⋙ F.1)) (hs : s ≠ s')
    (f : colimit (V.rightOp ⋙ uliftYoneda.{w}.obj W)) :
    ∃ (I : Type w) (_ : Preorder I) (_ : Nonempty I)
      (_ : IsDirected I (· ≤ ·)) (U : Iᵒᵖ ⥤ C) (e : J ↪o I)
      (h : e.toOrderHom.toFunctor ⋙ U.rightOp = V.rightOp),
      (((eqToHom (congrArg (fun X : J ⥤ Cᵒᵖ => colimit (X ⋙ F.1)) h).symm) ≫
          colimit.pre (U.rightOp ⋙ F.1) e.toOrderHom.toFunctor) s ≠
        ((eqToHom (congrArg (fun X : J ⥤ Cᵒᵖ => colimit (X ⋙ F.1)) h).symm) ≫
          colimit.pre (U.rightOp ⋙ F.1) e.toOrderHom.toFunctor) s') ∧
      (∃ k : K,
        ∃ g : colimit (U.rightOp ⋙ uliftYoneda.{w}.obj (Wk k)),
          colimMap (U.rightOp.whiskerLeft (uliftYoneda.map (wk k))) g =
            ((eqToHom (congrArg
                (fun X : J ⥤ Cᵒᵖ => colimit (X ⋙ uliftYoneda.{w}.obj W)) h).symm) ≫
              colimit.pre (U.rightOp ⋙ uliftYoneda.{w}.obj W) e.toOrderHom.toFunctor) f) := by
  classical
  -- Reindex the finite cover into the universe accepted by the site pullback axiom.
  let _ := Fintype.ofFinite K
  let A := ULift.{max u v} (Fin (Fintype.card K))
  let eK : A ≃ K := Equiv.ulift.trans (Fintype.equivFin K).symm
  have hc : Presieve.ofArrows (Wk ∘ eK) (fun k ↦ wk (eK k)) ∈ P W := by
    rwa [Presieve.ofArrows_comp_eq_of_surjective wk eK.surjective]
  obtain ⟨js, xs, ys, hxs, hys⟩ :=
    Types.FilteredColimit.jointly_surjective_of_isColimit₂ (colimit.isColimit _) s s'
  obtain ⟨jf, zf, hzf⟩ := Types.jointly_surjective' f
  obtain ⟨j₀, hsj, hfj⟩ := directed_of (· ≤ ·) js jf
  let x := (V.rightOp ⋙ F.1).map (homOfLE hsj) xs
  let y := (V.rightOp ⋙ F.1).map (homOfLE hsj) ys
  let f₀ : V.obj (Opposite.op j₀) ⟶ W :=
    V.map (homOfLE hfj).op ≫ zf.down
  have hx : colimit.ι (V.rightOp ⋙ F.1) j₀ x = s := by
    rw [← hxs]
    exact ConcreteCategory.congr_hom (colimit.w (V.rightOp ⋙ F.1) (homOfLE hsj)) xs
  have hy : colimit.ι (V.rightOp ⋙ F.1) j₀ y = s' := by
    rw [← hys]
    exact ConcreteCategory.congr_hom (colimit.w (V.rightOp ⋙ F.1) (homOfLE hsj)) ys
  have hf₀ : colimit.ι (V.rightOp ⋙ uliftYoneda.{w}.obj W) j₀ (ULift.up f₀) = f := by
    rw [← hzf]
    exact ConcreteCategory.congr_hom
      (colimit.w (V.rightOp ⋙ uliftYoneda.{w}.obj W) (homOfLE hfj)) zf
  let T := {j : J // j₀ ≤ j}
  let _ : Nonempty T := ⟨⟨j₀, le_rfl⟩⟩
  let _ : IsDirected T (· ≤ ·) := ⟨fun i j ↦ by
    obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i.val j.val
    exact ⟨⟨k, i.property.trans hik⟩, hik, hjk⟩⟩
  let D : Tᵒᵖ ⥤ C := (tailInclusion j₀).op ⋙ V
  let b : ∀ j : T, D.obj (Opposite.op j) ⟶ W :=
    fun j ↦ V.map (homOfLE j.property).op ≫ f₀
  have hb : ∀ {i j : T} (f : i ⟶ j), D.map f.op ≫ b i = b j := by
    intro i j f
    dsimp [D, b, tailInclusion]
    rw [← Category.assoc, ← V.map_comp]
    congr 2
  choose Q p q hp hcQ using fun j : T ↦
    hP.2.2 A W (Wk ∘ eK) (fun k ↦ wk (eK k)) hc
      (D.obj (Opposite.op j)) (b j)
  let B (k : A) := pullbackDiagram D (wk (eK k)) b hb
    (fun j ↦ Q j k) (fun j ↦ p j k) (fun j ↦ q j k) (fun j ↦ hp j k)
  let α (k : A) : tailInclusion j₀ ⋙ V.rightOp ⟶ B k :=
    pullbackTransformation D (wk (eK k)) b hb
      (fun j ↦ Q j k) (fun j ↦ p j k) (fun j ↦ q j k) (fun j ↦ hp j k)
  let G := tailInclusion j₀ ⋙ (V.rightOp ⋙ F.1)
  have hinj : ∀ j (x y : G.obj j),
      (∀ k, F.1.map ((α k).app j) x = F.1.map ((α k).app j) y) → x = y := by
    intro j x y he
    apply (((isSheaf_iff_isSheaf_of_type _ _).mp F.2).isSheafFor_of_mem_precoverage
      (hcQ j)).isSeparatedFor.ext
    rintro _ _ ⟨k⟩
    exact he k
  have hne : ∀ j (a : (⟨j₀, le_rfl⟩ : T) ⟶ j), G.map a x ≠ G.map a y := by
    intro j a he
    apply hs
    rw [← hx, ← hy]
    have hh := colimit.w (V.rightOp ⋙ F.1) ((tailInclusion j₀).map a)
    exact (ConcreteCategory.congr_hom hh x).symm.trans
      ((congrArg (colimit.ι (V.rightOp ⋙ F.1) j.val) he).trans
        (ConcreteCategory.congr_hom hh y))
  -- Finite common upper bounds give the needed finite-product argument elementwise.
  obtain ⟨k, hk⟩ := finite_persistent_ne G (fun k ↦ B k ⋙ F.1)
    (fun k ↦ Functor.whiskerRight (α k) F.1) hinj ⟨j₀, le_rfl⟩ x y hne
  let R := refineDiagram j₀ V.rightOp (B k) (α k)
  let U := R.leftOp
  let e := refineInclusion j₀
  have h : e.toOrderHom.toFunctor ⋙ U.rightOp = V.rightOp :=
    refineDiagram_restrict j₀ V.rightOp (B k) (α k)
  refine ⟨RefineIndex J j₀, inferInstance, inferInstance, inferInstance, U, e, h, ?_, ?_⟩
  · rw [← hx, ← hy]
    simp only [← types_comp_apply]
    rw [refinementMap_ι V.rightOp U.rightOp e h F.1]
    simp only [eqToHom_refl, Functor.map_id, Category.id_comp]
    -- Equality would already occur at a stage, hence at a later tail stage.
    intro he
    obtain ⟨i, a, a', he⟩ :=
      (Types.FilteredColimit.colimit_eq_iff (U.rightOp ⋙ F.1)).mp he
    have haa : a' = a := Subsingleton.elim _ _
    subst a'
    obtain ⟨l, hil, h₀l⟩ := directed_of (α := RefineIndex J j₀) (· ≤ ·) i
      (Sum.inr (⟨j₀, le_rfl⟩ : T))
    cases l with
    | inl l => exact h₀l.elim
    | inr l =>
      have he' := congrArg ((U.rightOp ⋙ F.1).map (homOfLE hil)) he
      simp only [← Functor.map_comp_apply] at he'
      change F.1.map (V.rightOp.map (homOfLE l.property) ≫ (α k).app l) x =
        F.1.map (V.rightOp.map (homOfLE l.property) ≫ (α k).app l) y at he'
      simp only [Functor.map_comp_apply] at he'
      exact hk l (homOfLE l.property) he'
  · refine ⟨eK k, colimit.ι (U.rightOp ⋙ uliftYoneda.{w}.obj (Wk (eK k)))
      (Sum.inr (⟨j₀, le_rfl⟩ : T)) (ULift.up (q ⟨j₀, le_rfl⟩ k)), ?_⟩
    rw [← hf₀]
    simp only [← types_comp_apply]
    rw [refinementMap_ι V.rightOp U.rightOp e h (uliftYoneda.{w}.obj W)]
    simp only [eqToHom_refl, Functor.map_id, Category.id_comp]
    rw [ι_colimMap]
    change colimit.ι (U.rightOp ⋙ uliftYoneda.{w}.obj W)
      (Sum.inr (⟨j₀, le_rfl⟩ : T)) (ULift.up (q ⟨j₀, le_rfl⟩ k ≫ wk (eK k))) =
        colimit.ι (U.rightOp ⋙ uliftYoneda.{w}.obj W) (e j₀) (ULift.up f₀)
    rw [← (hp ⟨j₀, le_rfl⟩ k).w]
    have hb₀ : b ⟨j₀, le_rfl⟩ = f₀ := by
      change V.map (𝟙 (Opposite.op j₀)) ≫ f₀ = f₀
      rw [V.map_id, Category.id_comp]
    rw [hb₀]
    have hcross : e j₀ ≤ (show RefineIndex J j₀ from Sum.inr (⟨j₀, le_rfl⟩ : T)) := le_rfl
    simpa [R, U, e, refineInclusion, refineDiagram, α, pullbackTransformation] using
      ConcreteCategory.congr_hom
        (colimit.w (U.rightOp ⋙ uliftYoneda.{w}.obj W) (homOfLE hcross))
        (ULift.up.{w} f₀ : ULift.{w} (V.obj (Opposite.op j₀) ⟶ W))

end CategoryTheory
