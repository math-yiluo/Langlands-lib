/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.ArrowsFunctor
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Comma.Over.Basic

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

import all WeilConjectures.CategoryTheory.ColimitSiteAbelianStageImageRefinement
import all WeilConjectures.CategoryTheory.ColimitSiteAbelianFiniteObjectSectionLift
import Mathlib.CategoryTheory.Filtered.Final

/-! # Finite raw section lifts

Source: Stacks Project, Sites, Tag 0A35.
(blueprint: lem-weil-pbc-colimit-site-raw-finite-sections-lift).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction

namespace CategoryTheory

private theorem kan_element
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (L : C ⥤ D) (A : C ⥤ Type u) (B : D ⥤ Type u) (β : A ⟶ L ⋙ B)
    [B.IsLeftKanExtension β] (Y : D) (x : B.obj Y) :
    ∃ (W : C) (f : L.obj W ⟶ Y) (s : A.obj W), B.map f (β.app W s) = x := by
  have h := Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension B β Y
  obtain ⟨g, s, hs⟩ := Types.jointly_surjective_of_isColimit h x
  exact ⟨g.left, g.hom, s, hs⟩

-- A raw section lifts once and remains representable at every further refinement.
private theorem one_raw_section
    (J : Type u) [SmallCategory J] [IsFiltered J] (F : J ⥤ Cat.{u, u})
    (V : Cocone F) (hobjects : IsColimit (Cat.objects.mapCocone V))
    (harrows : IsColimit (Cat.arrows.mapCocone V)) (i : J)
    (A : ∀ t : Under i, (F.obj t.right)ᵒᵖ ⥤ Type u)
    (θ : ∀ (t t' : Under i) (b : t ⟶ t'),
      A t ⟶ (F.map b.right).toFunctor.op ⋙ A t')
    (B : Under i ⥤ (V.ptᵒᵖ ⥤ Type u))
    (β : ∀ t : Under i, A t ⟶ (V.ι.app t.right).toFunctor.op ⋙ B.obj t)
    (hβ : ∀ t : Under i, (B.obj t).IsLeftKanExtension (β t))
    (hβmap : ∀ (t t' : Under i) (b : t ⟶ t') (X : F.obj t.right),
      Arrow.mk ((β t).app (op X) ≫
        (B.map b).app (op ((V.ι.app t.right).toFunctor.obj X))) =
      Arrow.mk ((θ t t' b).app (op X) ≫
        (β t').app (op ((F.map b.right).toFunctor.obj X))))
    (t0 : Under i) (Z : F.obj t0.right)
    (x : (colimit B).obj (op ((V.ι.app t0.right).toFunctor.obj Z))) :
    ∃ q : Under t0, ∀ (q' : Under t0) (_b : q ⟶ q'),
      ∃ y : (A q'.right).obj (op ((F.map q'.hom.right).toFunctor.obj Z)),
        ((β q'.right).app (op ((F.map q'.hom.right).toFunctor.obj Z)) ≫
          (colimit.ι B q'.right).app
            (op ((V.ι.app q'.right.right).toFunctor.obj
              ((F.map q'.hom.right).toFunctor.obj Z))) ≫
          eqToHom (congrArg (fun X ↦ (colimit B).obj (op X))
            (congrArg (fun K : F.obj t0.right ⟶ V.pt ↦ K.toFunctor.obj Z)
              (V.w q'.hom.right)))) y = x := by
  classical
  let H := colimit B
  let δ (t : Under i) := β t ≫
    Functor.whiskerLeft (V.ι.app t.right).toFunctor.op (colimit.ι B t)
  have hcone (t t' : Under i) (b : t ⟶ t') (T : F.obj t.right) :
      Arrow.mk ((θ t t' b).app (op T) ≫
        (δ t').app (op ((F.map b.right).toFunctor.obj T))) =
      Arrow.mk ((δ t).app (op T)) := by
    have hV : (V.ι.app t.right).toFunctor.obj T =
        (V.ι.app t'.right).toFunctor.obj ((F.map b.right).toFunctor.obj T) :=
      (congrArg (fun K : F.obj t.right ⟶ V.pt ↦ K.toFunctor.obj T) (V.w b.right)).symm
    have htransport : ∀ {Y Z : V.ptᵒᵖ} (e : Y = Z)
        (f : (A t).obj (op T) ⟶ (B.obj t').obj Y)
        (g : (A t).obj (op T) ⟶ (B.obj t').obj Z),
        Arrow.mk f = Arrow.mk g →
          Arrow.mk (f ≫ (colimit.ι B t').app Y) =
            Arrow.mk (g ≫ (colimit.ι B t').app Z) := by
      intro Y Z e f g h
      subst Z
      rw [Arrow.mk_injective _ _ h]
    have hh := htransport (congrArg op hV) _ _ (hβmap t t' b T)
    dsimp only [δ, NatTrans.comp_app, Functor.whiskerLeft_app]
    symm
    calc
      _ = Arrow.mk ((β t).app (op T) ≫ (B.map b).app
          (op ((V.ι.app t.right).toFunctor.obj T)) ≫ (colimit.ι B t').app
          (op ((V.ι.app t.right).toFunctor.obj T))) := by
        congr 1
        simp only [Functor.op_obj, ← NatTrans.comp_app, colimit.w]
      _ = _ := by
        simpa only [Category.assoc, Functor.op_obj] using hh
  let W (q : Under t0) := (F.map q.hom.right).toFunctor.obj Z
  let S (q : Under t0) := (A q.right).obj (op (W q))
  have hvo (q : Under t0) :
      (V.ι.app q.right.right).toFunctor.obj (W q) =
        (V.ι.app t0.right).toFunctor.obj Z :=
    congrArg (fun K : F.obj t0.right ⟶ V.pt ↦ K.toFunctor.obj Z) (V.w q.hom.right)
  let k (q : Under t0) : S q ⟶ H.obj (op ((V.ι.app t0.right).toFunctor.obj Z)) :=
    (δ q.right).app (op (W q)) ≫
      eqToHom (congrArg (fun X ↦ H.obj (op X)) (hvo q))
  have hw (q q' : Under t0) (b : q ⟶ q') :
      (F.map b.right.right).toFunctor.obj (W q) = W q' := by
    have hh : (F.map q.hom.right).toFunctor ⋙
        (F.map b.right.right).toFunctor = (F.map q'.hom.right).toFunctor := by
      change (F.map q.hom.right ≫ F.map b.right.right).toFunctor = _
      rw [← F.map_comp]
      exact congrArg (fun c : t0 ⟶ q'.right ↦ (F.map c.right).toFunctor) (Under.w b)
    exact congrArg (fun K ↦ K.obj Z) hh
  let m (q q' : Under t0) (b : q ⟶ q') : S q ⟶ S q' :=
    (θ q.right q'.right b.right).app (op (W q)) ≫
      eqToHom (congrArg (fun X ↦ (A q'.right).obj (op X)) (hw q q' b))
  have hmk (q q' : Under t0) (b : q ⟶ q') : m q q' b ≫ k q' = k q := by
    apply Arrow.mk_injective
    have hn := (δ q'.right).naturality (eqToHom (congrArg op (hw q q' b)))
    simp only [eqToHom_map] at hn
    dsimp only [m, k]
    rw [Category.assoc, ← Category.assoc (eqToHom _) _ _, hn]
    simp only [← Category.assoc, Arrow.arrow_mk_comp_eqToHom]
    exact hcone q.right q'.right b.right (W q)
  obtain ⟨t, z, hz⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves ((evaluation _ _).obj
      (op ((V.ι.app t0.right).toFunctor.obj Z))) (colimit.isColimit B)) x
  change (colimit.ι B t).app (op ((V.ι.app t0.right).toFunctor.obj Z)) z = x at hz
  have : (B.obj t).IsLeftKanExtension (β t) := hβ t
  obtain ⟨T, r, y, hy⟩ := kan_element (V.ι.app t.right).toFunctor.op
    (A t) (B.obj t) (β t) _ z
  obtain ⟨q, c, f, hf⟩ := restriction_at_stage J F V hobjects harrows
    i t0 t Z T.unop r.unop
  let z' := (θ t q.right c).app T y
  let y' : S q := (A q.right).map f.op z'
  have hk : k q y' = x := by
    have hc := hcone t q.right c T.unop
    have hn := NatTrans.naturality_apply (δ q.right) f.op z'
    change (δ q.right).app (op (W q)) y' =
      H.map ((V.ι.app q.right.right).toFunctor.map f).op
        ((δ q.right).app (op ((F.map c.right).toFunctor.obj T.unop)) z') at hn
    dsimp only [k]
    rw [types_comp_apply, hn]
    have hmap : Arrow.mk (H.map ((V.ι.app q.right.right).toFunctor.map f).op) =
        Arrow.mk (H.map r) :=
      congrArg (fun a : Arrow V.pt ↦ Arrow.mk (H.map a.hom.op)) hf
    have htotal : (θ t q.right c).app T ≫
        (δ q.right).app (op ((F.map c.right).toFunctor.obj T.unop)) ≫
        H.map ((V.ι.app q.right.right).toFunctor.map f).op ≫
        eqToHom (congrArg (fun X ↦ H.obj (op X)) (hvo q)) =
        (δ t).app T ≫ H.map r := by
      apply Arrow.mk_injective
      rw [← Category.assoc, ← Category.assoc, Arrow.arrow_mk_comp_eqToHom]
      exact arrow_comp_congr _ _ _ _ hc hmap
    have he := ConcreteCategory.congr_hom htotal y
    have hnat := (NatTrans.naturality_apply (colimit.ι B t) r ((β t).app T y)).symm
    change H.map r ((δ t).app T y) =
      (colimit.ι B t).app _ ((B.obj t).map r ((β t).app T y)) at hnat
    exact he.trans (hnat.trans (by rw [hy, hz]))
  refine ⟨q, ?_⟩
  intro q' b
  exact ⟨m q q' b y', (ConcreteCategory.congr_hom (hmk q q' b) y').trans hk⟩

private theorem untransport_raw
    {C : Type u} [SmallCategory C] (H : Cᵒᵖ ⥤ Type u)
    {X Y : C} (h : X = Y) (z : H.obj (op X)) (x : H.obj (op Y))
    (hz : eqToHom (congrArg (fun T ↦ H.obj (op T)) h) z = x) :
    z = H.map (eqToHom h).op x := by
  subst Y
  simpa using hz

set_option linter.unusedVariables false in
/-- Source: Stacks Project, Sites, Tag 0A35 (lemma-compute-pullback-to-limit),
the raw section presentation and finite-stage construction.
(blueprint: lem-weil-pbc-colimit-site-raw-finite-sections-lift).

Proof: Evaluation preserves the outer presheaf colimit, so each of the finitely
many given elements has a representative in some B(t). The pointwise Kan formula
represents it by a section at Z and an arrow from V(j)(Y(p)) to V(t)(Z).
Lift that arrow and its endpoint equalities using the arrow and object set colimits.
Move to a stage receiving j and t.right, and equalize the two maps from i so that
it is an object of Under i receiving t. Transport the section by theta and restrict
along the lifted arrow. Naturality of beta, the colimit coprojections and h-beta-map
identify its raw image with the given element transported along the cocone equality.
The unit condition identifies theta with the unique adjunction transpose, so these
transports compose. Filteredness gives a common refinement for the finite list of
representatives and equalizes the finitely many arrows from j. At this refinement
all elements are represented at F(a)(Y(p)). The cocone equation gives e for every
object of F(j). If the index is empty, take any common successor of i and j and the
empty family. No compatibility, covering family, or amalgamation is involved.
-/
theorem colimit_site_raw_finite_sections_lift
    (J : Type u) [SmallCategory J] [IsFiltered J] (F : J ⥤ Cat.{u, u})
    (P : ∀ j : J, Precoverage (F.obj j))
    [∀ (j k : J) (a : j ⟶ k),
      (F.map a).toFunctor.IsContinuous (P j).toGrothendieck (P k).toGrothendieck]
    (V : Cocone F)
    (hobjects : IsColimit (Cat.objects.mapCocone V))
    (harrows : IsColimit (Cat.arrows.mapCocone V))
    (Q : Precoverage V.pt)
    [∀ j : J, (V.ι.app j).toFunctor.IsContinuous
      (P j).toGrothendieck Q.toGrothendieck]
    (i : J) (G : Sheaf (P i).toGrothendieck (Type u))
    (θ : ∀ (t t' : Under i) (b : t ⟶ t'),
                        (sheafPullback (F.map t.hom).toFunctor (Type u)
                          (P i).toGrothendieck (P t.right).toGrothendieck).obj G ⟶
                        ((F.map b.right).toFunctor.sheafPushforwardContinuous (Type u)
                          (P t.right).toGrothendieck (P t'.right).toGrothendieck).obj
                          ((sheafPullback (F.map t'.hom).toFunctor (Type u)
                            (P i).toGrothendieck (P t'.right).toGrothendieck).obj G))
    (hθ : ∀ (t t' : Under i) (b : t ⟶ t'),
      (∀ X : F.obj i,
                          Arrow.mk
                            (((sheafAdjunctionContinuous (F.map t.hom).toFunctor (Type u)
                              (P i).toGrothendieck (P t.right).toGrothendieck).unit.app
                                G).hom.app (op X) ≫
                              (θ t t' b).hom.app (op ((F.map t.hom).toFunctor.obj X))) =
                          Arrow.mk
                            (((sheafAdjunctionContinuous (F.map t'.hom).toFunctor (Type u)
                              (P i).toGrothendieck (P t'.right).toGrothendieck).unit.app
                                G).hom.app (op X))))
    (B : Under i ⥤ (V.ptᵒᵖ ⥤ Type u))
    (β : ∀ t : Under i,
      ((sheafPullback (F.map t.hom).toFunctor (Type u)
        (P i).toGrothendieck (P t.right).toGrothendieck).obj G).obj ⟶
        (V.ι.app t.right).toFunctor.op ⋙ B.obj t)
    (hβ : ∀ t : Under i, (B.obj t).IsLeftKanExtension (β t))
    (hβmap : ∀ (t t' : Under i) (b : t ⟶ t') (X : F.obj t.right),
      Arrow.mk ((β t).app (op X) ≫
        (B.map b).app (op ((V.ι.app t.right).toFunctor.obj X))) =
      Arrow.mk ((θ t t' b).hom.app (op X) ≫
        (β t').app (op ((F.map b.right).toFunctor.obj X))))
    (j : J) (I : Type u) [Finite I] (Y : I → F.obj j)
    (x : ∀ p, (colimit B).obj (op ((V.ι.app j).toFunctor.obj (Y p)))) :
    ∃ (t : Under i) (a : j ⟶ t.right)
      (e : ∀ U : F.obj j,
        (V.ι.app t.right).toFunctor.obj ((F.map a).toFunctor.obj U) =
          (V.ι.app j).toFunctor.obj U)
      (s : ∀ p, ((sheafPullback (F.map t.hom).toFunctor (Type u)
        (P i).toGrothendieck (P t.right).toGrothendieck).obj G).obj.obj
          (op ((F.map a).toFunctor.obj (Y p)))),
      ∀ p, (colimit.ι B t).app
        (op ((V.ι.app t.right).toFunctor.obj ((F.map a).toFunctor.obj (Y p))))
        ((β t).app (op ((F.map a).toFunctor.obj (Y p))) (s p)) =
      (colimit B).map (eqToHom (e (Y p))).op (x p) := by
  classical
  let k := IsFiltered.max i j
  let ai : i ⟶ k := IsFiltered.leftToMax i j
  let aj : j ⟶ k := IsFiltered.rightToMax i j
  let t0 : Under i := Under.mk ai
  let A (t : Under i) := ((sheafPullback (F.map t.hom).toFunctor (Type u)
    (P i).toGrothendieck (P t.right).toGrothendieck).obj G).obj
  let H := colimit B
  have e0 (U : F.obj j) :
      (V.ι.app k).toFunctor.obj ((F.map aj).toFunctor.obj U) =
        (V.ι.app j).toFunctor.obj U :=
    congrArg (fun K : F.obj j ⟶ V.pt ↦ K.toFunctor.obj U) (V.w aj)
  have hlift (p : I) := one_raw_section J F V hobjects harrows i A
    (fun t t' b ↦ (θ t t' b).hom) B β hβ hβmap t0
    ((F.map aj).toFunctor.obj (Y p)) (H.map (eqToHom (e0 (Y p))).op (x p))
  choose q hq using hlift
  have : Fintype I := Fintype.ofFinite I
  let O : Finset (Under t0) := Finset.univ.image q
  obtain ⟨s, hs⟩ := IsFiltered.sup_objs_exists O
  have hb (p : I) : Nonempty (q p ⟶ s) := hs (by simp [O])
  let b (p : I) : q p ⟶ s := (hb p).some
  have hy (p : I) := hq p s (b p)
  choose y hy using hy
  let a : j ⟶ s.right.right := aj ≫ s.hom.right
  have es (U : F.obj j) : (V.ι.app s.right.right).toFunctor.obj
      ((F.map s.hom.right).toFunctor.obj ((F.map aj).toFunctor.obj U)) =
      (V.ι.app k).toFunctor.obj ((F.map aj).toFunctor.obj U) :=
    congrArg (fun K : F.obj k ⟶ V.pt ↦
      K.toFunctor.obj ((F.map aj).toFunctor.obj U)) (V.w s.hom.right)
  refine ⟨s.right, a, ?_⟩
  dsimp only [a]
  rw [F.map_comp]
  refine ⟨fun U ↦ (es U).trans (e0 U), y, ?_⟩
  intro p
  have he := hy p
  simp only [types_comp_apply] at he
  have hu := untransport_raw H (es (Y p)) _ _ he
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
    eqToHom_trans] at hu
  simp only [types_comp_apply, H] at hu
  convert hu using 1 <;> rfl

end CategoryTheory
