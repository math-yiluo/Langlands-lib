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
import Mathlib.CategoryTheory.Filtered.Final
import WeilConjectures.CategoryTheory.ColimitSiteKanUnitRelations

/-! # Finite raw section equality stabilization

Source: Stacks Project, Sites, Tag 0A35.
(blueprint: lem-weil-pbc-colimit-site-raw-finite-equality-stabilization).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction

namespace CategoryTheory

private theorem arrow_postcomp {C : Type u} [Category C]
    {S T : C ⥤ Type u} (δ : S ⟶ T) {A : Type u} {Y Z : C}
    (e : Y = Z) (f : A ⟶ S.obj Y) (g : A ⟶ S.obj Z)
    (h : Arrow.mk f = Arrow.mk g) :
    Arrow.mk (f ≫ δ.app Y) = Arrow.mk (g ≫ δ.app Z) := by
  subst Z
  rw [Arrow.mk_injective _ _ h]

private theorem arrow_eq_preserves_equality {S T U : Type u}
    (f : S ⟶ T) (g : S ⟶ U) (h : Arrow.mk f = Arrow.mk g)
    (x y : S) (hxy : f x = f y) : g x = g y := by
  have e := congrArg Arrow.right h
  change T = U at e
  subst U
  rw [← Arrow.mk_injective _ _ h]
  exact hxy

/-- Source: Stacks Project, Sites, Tag 0A35 (lemma-compute-pullback-to-limit),
finite overlap equalities in the filtered-colimit calculation.
(blueprint: lem-weil-pbc-colimit-site-raw-finite-equality-stabilization).

Proof: The unit condition htheta determines each theta uniquely by the sheaf
adjunction hom-equivalence. Consequently theta preserves identity and composition,
with the object transports supplied by F and the triangles in Under i.

For one p, evaluate the outer presheaf colimit at Y = V_t(X_p). Evaluation
preserves colimits and Under i is filtered, so equality of its two representatives
holds in B_k(Y) after one transition t -> k. By hbeta-map these are beta_k images
of theta-transported r_p and s_p, with the cocone object transport to Y.
The pointwise left Kan formula presents B_k(Y) by triples (W, a, x), with
W in F(k.right), a : Y -> V_k(W), and x a section at W. Equality is a finite
zigzag of relations identifying (W, a, restriction along h of x') with
(W', a followed by V_k(h), x'), for h : W -> W'.

Lift all the finitely many arrows a to a stage receiving k, using surjectivity
of the arrow cocone. Use eventual equality in the object cocone to align their
sources with the forward image of X_p and their targets with the forward images
of W. Refine again so eventual equality in the arrow cocone enforces each
relation triangle and identifies both endpoint arrows with the identity of
the forward image of X_p. Filteredness equalizes the competing stage maps,
including the maps from i, so this is one transition in Under i.
Send each triple to the section obtained by theta-transporting x and restricting
along its lifted arrow. Naturality of theta and the lifted triangles make the
two sides of each generating relation equal. Thus the zigzag endpoints agree;
the identity endpoint arrows and composition of theta identify them with the
original r_p and s_p transported through the composite transition from t.

Repeat this construction for each p. Since K is finite, filteredness supplies a
common receiving stage and equalizes the finitely many maps from t. Transport
of an equality remains an equality, and composition of theta gives every
required equation for that single transition. If K is empty, take the identity
of t. This argument uses no covering family, pullback, or gluing. -/
theorem colimit_site_raw_finite_equality_stabilization
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
    (t : Under i) (K : Type u) [Finite K] (X : K → F.obj t.right)
    (r s : ∀ p, ((sheafPullback (F.map t.hom).toFunctor (Type u)
      (P i).toGrothendieck (P t.right).toGrothendieck).obj G).obj.obj (op (X p)))
    (hrs : ∀ p,
      (colimit.ι B t).app (op ((V.ι.app t.right).toFunctor.obj (X p)))
          ((β t).app (op (X p)) (r p)) =
        (colimit.ι B t).app (op ((V.ι.app t.right).toFunctor.obj (X p)))
          ((β t).app (op (X p)) (s p))) :
    ∃ (t' : Under i) (b : t ⟶ t'), ∀ p,
      (θ t t' b).hom.app (op (X p)) (r p) =
        (θ t t' b).hom.app (op (X p)) (s p) := by
  classical
  let A (t : Under i) := (sheafPullback (F.map t.hom).toFunctor (Type u)
    (P i).toGrothendieck (P t.right).toGrothendieck).obj G
  let f {t t' : Under i} (b : t ⟶ t') := (F.map b.right).toFunctor
  have ef {t t' : Under i} (b : t ⟶ t') :
      (F.map t.hom).toFunctor ⋙ f b = (F.map t'.hom).toFunctor :=
    congrArg Cat.Hom.toFunctor
      ((F.map_comp t.hom b.right).symm.trans (congrArg F.map (Under.w b)))
  have ecomp {t t' t'' : Under i} (b : t ⟶ t') (c : t' ⟶ t'') :
      f b ⋙ f c = f (b ≫ c) :=
    congrArg Cat.Hom.toFunctor (F.map_comp b.right c.right).symm
  have hcomp {t t' t'' : Under i} (b : t ⟶ t') (c : t' ⟶ t'') :
      (θ t t' b).hom ≫ Functor.whiskerLeft (f b).op (θ t' t'' c).hom ≫
        eqToHom (congrArg (fun g ↦ g.op ⋙ (A t'').obj) (ecomp b c)) =
      (θ t t'' (b ≫ c)).hom := by
    let k : A t ⟶ ((f (b ≫ c)).sheafPushforwardContinuous (Type u)
        (P t.right).toGrothendieck (P t''.right).toGrothendieck).obj (A t'') :=
      ⟨(θ t t' b).hom ≫ Functor.whiskerLeft (f b).op (θ t' t'' c).hom ≫
        eqToHom (congrArg (fun g ↦ g.op ⋙ (A t'').obj) (ecomp b c))⟩
    suffices hk : k = θ t t'' (b ≫ c) from congrArg (fun a ↦ a.hom) hk
    apply ((sheafAdjunctionContinuous (F.map t.hom).toFunctor (Type u)
      (P i).toGrothendieck (P t.right).toGrothendieck).homEquiv G _).injective
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext X
    apply Arrow.mk_injective _ _
    have he : op ((f b).obj ((F.map t.hom).toFunctor.obj X.unop)) =
        op ((F.map t'.hom).toFunctor.obj X.unop) :=
      congrArg (fun g ↦ op (g.obj X.unop)) (ef b)
    have ht := arrow_postcomp (θ t' t'' c).hom he _ _ (hθ t t' b X.unop)
    simpa [k, NatTrans.comp_app, Functor.whiskerLeft_app, eqToHom_app, ← Category.assoc]
      using ht.trans ((hθ t' t'' c X.unop).trans (hθ t t'' (b ≫ c) X.unop).symm)
  have hone (p : K) : ∃ (t' : Under i) (b : t ⟶ t'),
      (θ t t' b).hom.app (op (X p)) (r p) =
        (θ t t' b).hom.app (op (X p)) (s p) := by
    let Y := (V.ι.app t.right).toFunctor.obj (X p)
    let ev := (evaluation V.ptᵒᵖ (Type u)).obj (op Y)
    have hc := isColimitOfPreserves ev (colimit.isColimit B)
    have hh : (ev.mapCocone (colimit.cocone B)).ι.app t
        ((β t).app (op (X p)) (r p)) =
        (ev.mapCocone (colimit.cocone B)).ι.app t
          ((β t).app (op (X p)) (s p)) := hrs p
    obtain ⟨k, b, hb⟩ := (Types.FilteredColimit.isColimit_eq_iff' hc _ _).mp hh
    have hβk : (β k).app (op ((f b).obj (X p)))
        ((θ t k b).hom.app (op (X p)) (r p)) =
        (β k).app (op ((f b).obj (X p)))
          ((θ t k b).hom.app (op (X p)) (s p)) :=
      arrow_eq_preserves_equality _ _ (hβmap t k b (X p)) (r p) (s p) hb
    obtain ⟨k', c, hc'⟩ := raw_section_kan_unit_relations J F V hobjects harrows i k
      (fun a ↦ (A a).obj) (fun a c ↦ (θ k a c).hom) (B.obj k) (β k) (hβ k)
      ((f b).obj (X p)) _ _ hβk
    refine ⟨k', b ≫ c, ?_⟩
    have h := NatTrans.congr_app (hcomp b c) (op (X p))
    have hr := ConcreteCategory.congr_hom h (r p)
    have hs := ConcreteCategory.congr_hom h (s p)
    exact hr.symm.trans ((congrArg
      ((eqToHom (congrArg (fun g ↦ g.op ⋙ (A k').obj) (ecomp b c))).app (op (X p)))
      hc').trans hs)
  choose k b hb using hone
  obtain ⟨k', b', c, hc⟩ := IsFiltered.wideSpan b
  refine ⟨k', b', fun p ↦ ?_⟩
  have h := NatTrans.congr_app (hcomp (b p) (c p)) (op (X p))
  have hr := ConcreteCategory.congr_hom h (r p)
  have hs := ConcreteCategory.congr_hom h (s p)
  rw [← hc p]
  exact hr.symm.trans ((congrArg
    ((eqToHom (congrArg (fun g ↦ g.op ⋙ (A k').obj) (ecomp (b p) (c p)))).app
      (op (X p)))
    (congrArg ((θ (k p) k' (c p)).hom.app (op ((f (b p)).obj (X p)))) (hb p))).trans hs)


end CategoryTheory
