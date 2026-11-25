/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.CategoryTheory.Sites.Sheaf
import WeilConjectures.CategoryTheory.PointSystemRefineAll
import Mathlib.CategoryTheory.Filtered.Grothendieck
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.Shapes.Grothendieck
import Mathlib.CategoryTheory.Skeletal
import Mathlib.CategoryTheory.Limits.Final

/-!
# Countable saturation of inverse systems

Source: Stacks Project, Sites, Tags 00YP and 00YQ. Apply the all-at-once
refinement countably often, so that finite covers lift all germs of the union.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite ConcreteCategory

namespace CategoryTheory

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private def overUnion {T : Cat.{u, u}} (S : ℕ ⥤ Over T) :
    Grothendieck (S ⋙ Over.forget T) ⥤ T where
  obj X := (S.obj X.base).hom.toFunctor.obj X.fiber
  map {X Y} f :=
    eqToHom (congrArg (fun G : (S.obj X.base).left ⥤ T ↦ G.obj X.fiber)
      (congrArg Cat.Hom.toFunctor (Over.w (S.map f.base))).symm) ≫
        (S.obj Y.base).hom.toFunctor.map f.fiber
  map_id X := by simp [eqToHom_map]
  map_comp {X Y Z} f g := by
    have h := (congrArg Cat.Hom.toFunctor (Over.w (S.map g.base))).symm
    have hn := (eqToHom h).naturality f.fiber
    simp only [eqToHom_app, Cat.Hom.comp_toFunctor, Functor.comp_map] at hn
    simp only [Grothendieck.comp_base, Grothendieck.comp_fiber, Functor.map_comp,
      eqToHom_map, Category.assoc]
    rw [reassoc_of% hn]
    simp

private lemma overUnion_restrict {T : Cat.{u, u}} (S : ℕ ⥤ Over T) (n : ℕ) :
    Grothendieck.ι (S ⋙ Over.forget T) n ⋙ overUnion S = (S.obj n).hom.toFunctor := by
  refine Functor.ext
    (F := Grothendieck.ι (S ⋙ Over.forget T) n ⋙ overUnion S)
    (G := (S.obj n).hom.toFunctor) (fun _ ↦ rfl) ?_
  intro X Y f
  simp [overUnion, Grothendieck.ι, eqToHom_map]

private lemma colimit_transport {I : Type u} [SmallCategory I]
    (P : I ⥤ Type w) [HasColimit P] {i j : I} (h : i = j) {X : Type w}
    (a : X = P.obj i) (b : X = P.obj j) :
    eqToHom a ≫ colimit.ι P i = eqToHom b ≫ colimit.ι P j := by
  subst j
  rfl

private structure GermSystem {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (F : Sheaf J (Type (max u w))) where
  I : Type u
  order : PartialOrder I
  nonempty : Nonempty I
  directed : IsDirectedOrder I
  diagram : I ⥤ Cᵒᵖ
  first : colimit (diagram ⋙ F.obj)
  second : colimit (diagram ⋙ F.obj)
  distinct : first ≠ second

attribute [instance] GermSystem.order GermSystem.nonempty GermSystem.directed

/- Countable iteration of the refinement lemma gives an inverse system lifting every
finite covering and retaining two distinct section germs.
Source: Stacks Project, Sites, Tags 00YP and 00YQ
(auxiliary; not a blueprint node).

Proof: start with the singleton system at W. Repeatedly apply 00YP to the two germs,
and form the Grothendieck construction of the resulting sequence of directed index
posets. It is filtered. Its colimit is the sequential colimit of the stage colimits;
equality there is witnessed at a finite stage, so distinctness survives. Every Hom
germ is represented at one finite stage and lifts through every finite covering at
the next stage. Thus every Hom germ of the union has the required lift. -/
private theorem exists_filteredSystem_finiteCoverLifting
    {C : Type u} [SmallCategory C] (J : Precoverage C) (hJ : J.IsSiteForCoverings)
    (F : Sheaf J.toGrothendieck (Type (max u w))) (W : C)
    (s s' : F.obj.obj (op W)) (hne : s ≠ s') :
    ∃ (I : Type u) (_ : SmallCategory I) (_ : IsFiltered I) (_ : Quiver.IsThin I)
      (U : I ⥤ Cᵒᵖ) (i : I) (a : (U.obj i).unop ⟶ W),
      colimit.ι (U ⋙ F.obj) i (F.obj.map a.op s) ≠
        colimit.ι (U ⋙ F.obj) i (F.obj.map a.op s') ∧
      ∀ (n : ℕ) (X : C) (V : Fin n → C) (f : ∀ k, V k ⟶ X),
        Presieve.ofArrows V f ∈ J X →
        ∀ x : colimit (U ⋙ uliftYoneda.{u}.obj X),
          ∃ (k : Fin n) (y : colimit (U ⋙ uliftYoneda.{u}.obj (V k))),
            colimMap (U.whiskerLeft (uliftYoneda.map (f k))) y = x := by
  classical
  let V₀ : PUnit.{u + 1} ⥤ Cᵒᵖ := (Functor.const _).obj (op W)
  let c₀ : Cocone (V₀ ⋙ F.obj) :=
    { pt := F.obj.obj (op W)
      ι := { app := fun _ ↦ 𝟙 _, naturality := by intros; simp [V₀] } }
  have hi₀ : Function.Injective (colimit.ι (V₀ ⋙ F.obj) PUnit.unit) := by
    intro x y h
    have he := congrArg (fun t ↦ colimit.desc _ c₀ t) h
    simpa [← comp_apply, colimit.ι_desc, c₀, V₀] using he
  let initial : GermSystem F :=
    { I := PUnit.{u + 1}
      order := inferInstance
      nonempty := inferInstance
      directed := inferInstance
      diagram := V₀
      first := colimit.ι (V₀ ⋙ F.obj) PUnit.unit s
      second := colimit.ι (V₀ ⋙ F.obj) PUnit.unit s'
      distinct := fun h ↦ hne (hi₀ h) }
  have step (A : GermSystem F) :
      ∃ (B : GermSystem F) (e : A.I ↪o B.I)
        (h : A.diagram = e.monotone.functor ⋙ B.diagram),
        B.first = pointSystemRefinementMap A.diagram B.diagram e h F.obj A.first ∧
        B.second = pointSystemRefinementMap A.diagram B.diagram e h F.obj A.second ∧
        ∀ (n : ℕ) (X : C) (V : Fin n → C) (f : ∀ k, V k ⟶ X),
          Presieve.ofArrows V f ∈ J X →
          ∀ x : colimit (A.diagram ⋙ uliftYoneda.{u}.obj X),
            ∃ (k : Fin n) (i : B.I) (b : (B.diagram.obj i).unop ⟶ V k),
              pointSystemRefinementMap A.diagram B.diagram e h
                (uliftYoneda.{u}.obj X) x =
                  colimit.ι (B.diagram ⋙ uliftYoneda.{u}.obj X) i
                    (ULift.up (b ≫ f k)) := by
    obtain ⟨I, po, ne, di, U, e, h, hs, hl⟩ :=
      exists_pointSystem_refinement_all J hJ A.diagram F A.first A.second A.distinct
    exact ⟨⟨I, po, ne, di, U, _, _, hs⟩, e, h, rfl, rfl, hl⟩
  choose next e h hf hg hl using step
  let sys : ℕ → GermSystem F := Nat.rec initial (fun _ A ↦ next A)
  let (n : ℕ) : PartialOrder (sys n).I := (sys n).order
  let (n : ℕ) : SmallCategory (sys n).I :=
    @Preorder.smallCategory (sys n).I (sys n).order.toPreorder
  let obj (n : ℕ) : Over (Cat.of Cᵒᵖ) := by
    let := (sys n).order
    exact Over.mk (sys n).diagram.toCatHom
  let transition (n : ℕ) : obj n ⟶ obj (n + 1) := by
    let := (sys n).order
    let := (sys (n + 1)).order
    exact Over.homMk (e (sys n)).monotone.functor.toCatHom
      (congrArg Functor.toCatHom (h (sys n)).symm)
  let S : ℕ ⥤ Over (Cat.of Cᵒᵖ) := Functor.ofSequence transition
  let A := S ⋙ Over.forget (Cat.of Cᵒᵖ)
  have (n : ℕ) : IsFiltered (A.obj n) :=
    @isFiltered_of_directed_le_nonempty (sys n).I (sys n).order.toPreorder
      (sys n).directed (sys n).nonempty
  let U := overUnion S
  let P := U ⋙ F.obj
  let Q := fiberwiseColimit P
  let bridge (n : ℕ) : colimit ((sys n).diagram ⋙ F.obj) ≅ Q.obj n :=
    HasColimit.isoOfNatIso (eqToIso (by
      change (sys n).diagram ⋙ F.obj = Grothendieck.ι A n ⋙ (U ⋙ F.obj)
      rw [← Functor.assoc, overUnion_restrict]
      rfl))
  have bridge_ι (n : ℕ) (i : (sys n).I) :
      colimit.ι ((sys n).diagram ⋙ F.obj) i ≫ (bridge n).hom =
        colimit.ι (Grothendieck.ι A n ⋙ P) i := by
    dsimp only [bridge]
    rw [HasColimit.ι_isoOfNatIso_hom]
    simp [eqToHom_app, A]
  let first (n : ℕ) : Q.obj n := (bridge n).hom (sys n).first
  let second (n : ℕ) : Q.obj n := (bridge n).hom (sys n).second
  have bridge_step (n : ℕ) :
      (bridge n).hom ≫ Q.map (homOfLE n.le_succ) =
        @pointSystemRefinementMap C _ (sys n).I (sys n).order
          (sys (n + 1)).I (sys (n + 1)).order
          (sys n).diagram (sys (n + 1)).diagram (e (sys n)) (h (sys n)) F.obj _ _ _ ≫
            (bridge (n + 1)).hom := by
    let := (sys n).order
    let := (sys (n + 1)).order
    apply colimit.hom_ext
    intro i
    have hs : S.map (homOfLE n.le_succ) = transition n :=
      Functor.ofSequence_map_homOfLE_succ transition n
    simp only [Functor.comp_obj, fiberwiseColimit, Over.forget_obj, Cat.of_α, overUnion,
      Cat.Hom.comp_toFunctor, Functor.comp_map, Over.forget_map, Nat.succ_eq_add_one,
      homOfLE_leOfHom, HasColimit.ι_isoOfNatIso_hom_assoc, Grothendieck.ι_obj,
      eqToIso.hom, eqToHom_app, eqToHom_refl, ι_colimMap_assoc, NatTrans.comp_app,
      Functor.whiskerRight_app, Grothendieck.ιNatTrans_app_base,
      Grothendieck.ιNatTrans_app_fiber, Functor.map_id, Category.comp_id, eqToHom_map,
      Functor.associator_hom_app, colimit.ι_pre, Category.id_comp,
      pointSystemRefinementMap, Category.assoc, Monotone.functor_obj,
      colimit.ι_pre_assoc, HasColimit.ι_isoOfNatIso_hom, P, bridge, obj, Q, U]
    dsimp only [Grothendieck.ι]
    simp only [Functor.comp_obj, homOfLE_leOfHom]
    have he := congrArg (fun t : obj n ⟶ obj (n + 1) ↦ t.left.toFunctor.obj i) hs
    change (Over.Hom.left (S.map (homOfLE n.le_succ))).toFunctor.obj i =
      (e (sys n)) i at he
    exact colimit_transport (Grothendieck.ι A (n + 1) ⋙ P) he _ _
  have first_step (n : ℕ) : Q.map (homOfLE n.le_succ) (first n) = first (n + 1) := by
    change Q.map (homOfLE n.le_succ) ((bridge n).hom (sys n).first) = _
    rw [← comp_apply, bridge_step, comp_apply, ← hf]
  have second_step (n : ℕ) : Q.map (homOfLE n.le_succ) (second n) = second (n + 1) := by
    change Q.map (homOfLE n.le_succ) ((bridge n).hom (sys n).second) = _
    rw [← comp_apply, bridge_step, comp_apply, ← hg]
  let ft : (Functor.const ℕ).obj PUnit.{max u w + 1} ⟶ Q :=
    NatTrans.ofSequence (fun n ↦ TypeCat.ofHom (fun _ ↦ first n))
      (by intro n; ext z; simpa using (first_step n).symm)
  let st : (Functor.const ℕ).obj PUnit.{max u w + 1} ⟶ Q :=
    NatTrans.ofSequence (fun n ↦ TypeCat.ofHom (fun _ ↦ second n))
      (by intro n; ext z; simpa using (second_step n).symm)
  have hseq : colimit.ι Q 0 (first 0) ≠ colimit.ι Q 0 (second 0) := by
    intro he
    obtain ⟨n, f, hn⟩ := (Types.FilteredColimit.isColimit_eq_iff'
      (colimit.isColimit Q) _ _).1 he
    have hf' := congr_hom (ft.naturality f) PUnit.unit
    have hg' := congr_hom (st.naturality f) PUnit.unit
    change first n = Q.map f (first 0) at hf'
    change second n = Q.map f (second 0) at hg'
    have he' : first n = second n := hf'.trans (hn.trans hg'.symm)
    exact (sys n).distinct ((bridge n).toEquiv.injective he')
  have hfinal : colimit.ι P ⟨0, PUnit.unit⟩ s ≠
      colimit.ι P ⟨0, PUnit.unit⟩ s' := by
    intro he
    apply hseq
    apply (colimitFiberwiseColimitIso P).toEquiv.injective
    have hh (z : F.obj.obj (op W)) :
        (colimitFiberwiseColimitIso P).hom
          (colimit.ι Q 0 ((bridge 0).hom
            (colimit.ι (V₀ ⋙ F.obj) PUnit.unit z))) =
          colimit.ι P ⟨0, PUnit.unit⟩ z := by
      have ht := ι_colimitFiberwiseColimitIso_hom P 0 PUnit.unit
      rw [← bridge_ι] at ht
      exact congr_hom ht z
    exact (hh s).trans (he.trans (hh s').symm)
  have (n : ℕ) : Quiver.IsThin (A.obj n) := by
    let := (sys n).order
    change Quiver.IsThin (sys n).I
    infer_instance
  have : Quiver.IsThin (Grothendieck A) := fun _ _ ↦ ⟨fun f g ↦
    Grothendieck.ext f g (Subsingleton.elim _ _) (Subsingleton.elim _ _)⟩
  refine ⟨Grothendieck A, inferInstance, inferInstance, inferInstance, U,
    ⟨0, PUnit.unit⟩, 𝟙 W, ?_, ?_⟩
  · change colimit.ι P ⟨0, PUnit.unit⟩ (F.obj.map (𝟙 (op W)) s) ≠
      colimit.ι P ⟨0, PUnit.unit⟩ (F.obj.map (𝟙 (op W)) s')
    simpa only [Functor.map_id, ConcreteCategory.id_apply] using hfinal
  intro n X V f hc x
  let R := uliftYoneda.{u}.obj X
  let H := U ⋙ R
  let HQ := fiberwiseColimit H
  let hb (m : ℕ) : colimit ((sys m).diagram ⋙ R) ≅ HQ.obj m :=
    HasColimit.isoOfNatIso (eqToIso (by
      change (sys m).diagram ⋙ R = Grothendieck.ι A m ⋙ (U ⋙ R)
      rw [← Functor.assoc, overUnion_restrict]
      rfl))
  have hb_ι (m : ℕ) (i : (sys m).I) :
      colimit.ι ((sys m).diagram ⋙ R) i ≫ (hb m).hom =
        colimit.ι (Grothendieck.ι A m ⋙ H) i := by
    dsimp only [hb]
    rw [HasColimit.ι_isoOfNatIso_hom]
    simp [eqToHom_app, A]
  have hb_step (m : ℕ) :
      (hb m).hom ≫ HQ.map (homOfLE m.le_succ) =
        @pointSystemRefinementMap C _ (sys m).I (sys m).order
          (sys (m + 1)).I (sys (m + 1)).order
          (sys m).diagram (sys (m + 1)).diagram (e (sys m)) (h (sys m)) R _ _ _ ≫
            (hb (m + 1)).hom := by
    let := (sys m).order
    let := (sys (m + 1)).order
    apply colimit.hom_ext
    intro i
    have hs : S.map (homOfLE m.le_succ) = transition m :=
      Functor.ofSequence_map_homOfLE_succ transition m
    simp only [Functor.comp_obj, fiberwiseColimit, Over.forget_obj, Cat.of_α, overUnion,
      Cat.Hom.comp_toFunctor, Functor.comp_map, Over.forget_map, Nat.succ_eq_add_one,
      homOfLE_leOfHom, HasColimit.ι_isoOfNatIso_hom_assoc, Grothendieck.ι_obj,
      eqToIso.hom, eqToHom_app, eqToHom_refl, ι_colimMap_assoc, NatTrans.comp_app,
      Functor.whiskerRight_app, Grothendieck.ιNatTrans_app_base,
      Grothendieck.ιNatTrans_app_fiber, Functor.map_id, Category.comp_id, eqToHom_map,
      Functor.associator_hom_app, colimit.ι_pre, Category.id_comp,
      pointSystemRefinementMap, Category.assoc, Monotone.functor_obj,
      colimit.ι_pre_assoc, HasColimit.ι_isoOfNatIso_hom, H, hb, obj, U, HQ]
    dsimp only [Grothendieck.ι]
    have he := congrArg (fun t : obj m ⟶ obj (m + 1) ↦ t.left.toFunctor.obj i) hs
    change (Over.Hom.left (S.map (homOfLE m.le_succ))).toFunctor.obj i =
      (e (sys m)) i at he
    exact colimit_transport (Grothendieck.ι A (m + 1) ⋙ H) he _ _
  let k (m : ℕ) : colimit ((sys m).diagram ⋙ R) ⟶ colimit H :=
    (hb m).hom ≫ colimit.ι HQ m ≫ (colimitFiberwiseColimitIso H).hom
  have k_ι (m : ℕ) (i : (sys m).I) :
      colimit.ι ((sys m).diagram ⋙ R) i ≫ k m = colimit.ι H ⟨m, i⟩ := by
    dsimp only [k]
    rw [← Category.assoc, ← Category.assoc, hb_ι]
    exact ι_colimitFiberwiseColimitIso_hom H m i
  have k_step (m : ℕ) :
      @pointSystemRefinementMap C _ (sys m).I (sys m).order
          (sys (m + 1)).I (sys (m + 1)).order
          (sys m).diagram (sys (m + 1)).diagram (e (sys m)) (h (sys m)) R _ _ _ ≫
        k (m + 1) = k m := by
    dsimp only [k]
    rw [← Category.assoc, ← Category.assoc, ← hb_step]
    simp only [Category.assoc, colimit.w_assoc]
  obtain ⟨⟨m, i⟩, z, rfl⟩ := Types.jointly_surjective' x
  obtain ⟨j, l, b, hb'⟩ := hl (sys m) n X V f hc
    (colimit.ι ((sys m).diagram ⋙ R) i z)
  refine ⟨j, colimit.ι (U ⋙ uliftYoneda.{u}.obj (V j)) ⟨m + 1, l⟩
    (ULift.up b), ?_⟩
  have he := congrArg (fun t ↦ k (m + 1) t) hb'
  rw [← comp_apply, k_step] at he
  rw [← comp_apply, k_ι] at he
  let z' : ((sys (m + 1)).diagram ⋙ R).obj l := ULift.up (b ≫ f j)
  have he₂ := congr_hom (k_ι (m + 1) l) z'
  have he' := he.trans he₂
  rw [← comp_apply, ι_colimMap, comp_apply]
  exact he'.symm

/-- Countable refinement produces a directed inverse system which retains the given
unequal sections and lifts every finite covering.
Source: Stacks Project, Sites, Tags 00YP and 00YQ
(auxiliary; not a blueprint node).

Proof: iterate simultaneous refinement and use the filtered Grothendieck union. Its
colimit is the sequential colimit of the stage colimits, so equality is witnessed at
one stage. Each Hom germ occurs at a stage and lifts at the next. The union is thin;
replace it by its thin skeleton to obtain a directed partially ordered index type.
Equivalence of index categories preserves all the stated colimit properties. -/
theorem exists_pointSystem_finiteCoverLifting
    {C : Type u} [SmallCategory C] (J : Precoverage C) (hJ : J.IsSiteForCoverings)
    (F : Sheaf J.toGrothendieck (Type (max u w))) (W : C)
    (s s' : F.obj.obj (op W)) (hne : s ≠ s') :
    ∃ (I : Type u) (_ : PartialOrder I) (_ : Nonempty I) (_ : IsDirectedOrder I)
      (U : I ⥤ Cᵒᵖ) (i : I) (a : (U.obj i).unop ⟶ W),
      colimit.ι (U ⋙ F.obj) i (F.obj.map a.op s) ≠
        colimit.ι (U ⋙ F.obj) i (F.obj.map a.op s') ∧
      ∀ (n : ℕ) (X : C) (V : Fin n → C) (f : ∀ k, V k ⟶ X),
        Presieve.ofArrows V f ∈ J X →
        ∀ x : colimit (U ⋙ uliftYoneda.{u}.obj X),
          ∃ (k : Fin n) (y : colimit (U ⋙ uliftYoneda.{u}.obj (V k))),
            colimMap (U.whiskerLeft (uliftYoneda.map (f k))) y = x := by
  classical
  obtain ⟨I, cat, filt, thin, U, i, a, hd, hl⟩ :=
    exists_filteredSystem_finiteCoverLifting J hJ F W s s' hne
  let E := ThinSkeleton.equivalence I
  have : IsFiltered (ThinSkeleton I) := IsFiltered.of_equivalence E.symm
  have : Nonempty (ThinSkeleton I) := ⟨E.inverse.obj i⟩
  have : IsDirectedOrder (ThinSkeleton I) := IsFiltered.isDirectedOrder _
  let V := E.functor ⋙ U
  let j := E.inverse.obj i
  let b : (V.obj j).unop ⟶ W := (U.map (E.counitIso.inv.app i)).unop ≫ a
  refine ⟨ThinSkeleton I, inferInstance, inferInstance, inferInstance, V, j, b, ?_, ?_⟩
  · have ht (z : F.obj.obj (op W)) :
        colimit.pre (U ⋙ F.obj) E.functor
          (colimit.ι (V ⋙ F.obj) j (F.obj.map b.op z)) =
            colimit.ι (U ⋙ F.obj) i (F.obj.map a.op z) := by
      change colimit.pre (U ⋙ F.obj) E.functor
        (colimit.ι (E.functor ⋙ (U ⋙ F.obj)) j
          (F.obj.map (a.op ≫ U.map (E.counitIso.inv.app i)) z)) = _
      rw [Functor.map_comp, comp_apply, ← comp_apply, colimit.ι_pre]
      exact congr_hom (colimit.w (U ⋙ F.obj) (E.counitIso.inv.app i))
        (F.obj.map a.op z)
    intro he
    exact hd ((ht s).symm.trans ((congrArg
      (fun z ↦ colimit.pre (U ⋙ F.obj) E.functor z) he).trans (ht s')))
  intro n X Wk f hc x
  obtain ⟨k, y, hy⟩ := hl n X Wk f hc
    (colimit.pre (U ⋙ uliftYoneda.{u}.obj X) E.functor x)
  let q := colimit.pre (U ⋙ uliftYoneda.{u}.obj (Wk k)) E.functor
  let y' := (asIso q).inv y
  refine ⟨k, y', ?_⟩
  apply (asIso (colimit.pre (U ⋙ uliftYoneda.{u}.obj X) E.functor)).toEquiv.injective
  have hn := congr_hom
    (colimit.pre_map (U.whiskerLeft (uliftYoneda.map (f k))) E.functor) y'
  have hq : q y' = y := by
    change ((asIso q).inv ≫ q) y = y
    simp
  refine hn.symm.trans ?_
  change colimMap (U.whiskerLeft (uliftYoneda.map (f k))) (q y') = _
  rw [hq]
  exact hy

end CategoryTheory
