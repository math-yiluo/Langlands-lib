import Langlands.AlgebraicGeometry.Modules.CommonSourceCocycle

/-! # Pullback comparisons normalized on a common refinement -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.SchemeModule.RigidifiedModule

universe u

namespace Langlands.Scheme.Modules.RefinedPullbackComparison

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Normalize the pullback of a piece using its identification on a refinement. -/
def normalize {V K A : Scheme.{u}} (q : V ⟶ K) (a : K ⟶ A) (f : V ⟶ A)
    (h : q ≫ a = f) {M : A.Modules} {N : K.Modules}
    (e : (Scheme.Modules.pullback a).obj M ≅ N) :
    (Scheme.Modules.pullback f).obj M ≅ (Scheme.Modules.pullback q).obj N :=
  (asIso (compHom q a f h M)).symm ≪≫ (Scheme.Modules.pullback q).mapIso e

/-- Normalize both legs of an overlap through one refinement module. -/
def transition {V K A B : Scheme.{u}} (q : V ⟶ K)
    (a : K ⟶ A) (b : K ⟶ B) (f : V ⟶ A) (g : V ⟶ B)
    (ha : q ≫ a = f) (hb : q ≫ b = g) {M : A.Modules} {N : B.Modules} {P : K.Modules}
    (ea : (Scheme.Modules.pullback a).obj M ≅ P)
    (eb : (Scheme.Modules.pullback b).obj N ≅ P) :
    (Scheme.Modules.pullback f).obj M ≅ (Scheme.Modules.pullback g).obj N :=
  normalize q a f ha ea ≪≫ (normalize q b g hb eb).symm

/-- Refining a normalization commutes with the canonical square comparison. -/
lemma normalize_refine {W V K L A : Scheme.{u}}
    (t : W ⟶ V) (q : V ⟶ K) (r : W ⟶ L) (c : L ⟶ K)
    (a : K ⟶ A) (f : V ⟶ A) (a' : L ⟶ A) (p : W ⟶ A)
    (ht : t ≫ q = r ≫ c) (hf : q ≫ a = f) (ha : c ≫ a = a')
    (hp : t ≫ f = p) (hp' : r ≫ a' = p)
    {M : A.Modules} {N : K.Modules} {P : L.Modules}
    (e : (Scheme.Modules.pullback a).obj M ≅ N)
    (e' : (Scheme.Modules.pullback c).obj N ≅ P)
    (e'' : (Scheme.Modules.pullback a').obj M ≅ P)
    (he : (Scheme.Modules.pullback c).map e.hom ≫ e'.hom =
      compHom c a a' ha M ≫ e''.hom) :
    (Scheme.Modules.pullback t).map (normalize q a f hf e).hom ≫
        (squarePullbackIso c t r q ht N).hom ≫ (Scheme.Modules.pullback r).map e'.hom =
      compHom t f p hp M ≫ (normalize r a' p hp' e'').hom := by
  subst f a'
  simp only [compHom_rfl] at he
  have H := CommonSourceCocycle.outer_square_normalize t r q c a ht M p hp hp'
  simp only [CommonSourceCocycle.normalize] at H
  rw [← cancel_epi ((Scheme.Modules.pullback t).map
    ((Scheme.Modules.pullbackComp q a).hom.app M))]
  simp only [normalize, compHom_rfl, Iso.trans_hom, Iso.symm_hom, asIso_inv,
    Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc, IsIso.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.id_comp]
  rw [reassoc_of% (CommonSourceCocycle.square_naturality c t r q ht e.hom)]
  rw [← Functor.map_comp, he, Functor.map_comp]
  rw [← reassoc_of% H]
  simp

/-- A transition preserves normalization on every compatible further refinement. -/
lemma transition_normalize {W V K L A B : Scheme.{u}}
    (t : W ⟶ V) (q : V ⟶ K) (r : W ⟶ L) (c : L ⟶ K)
    (a : K ⟶ A) (b : K ⟶ B) (f : V ⟶ A) (g : V ⟶ B)
    (a' : L ⟶ A) (b' : L ⟶ B) (p : W ⟶ A) (s : W ⟶ B)
    (ht : t ≫ q = r ≫ c) (hf : q ≫ a = f) (hg : q ≫ b = g)
    (ha : c ≫ a = a') (hb : c ≫ b = b')
    (hp : t ≫ f = p) (hs : t ≫ g = s) (hp' : r ≫ a' = p) (hs' : r ≫ b' = s)
    {Ma : A.Modules} {Mb : B.Modules} {N : K.Modules} {P : L.Modules}
    (ea : (Scheme.Modules.pullback a).obj Ma ≅ N)
    (eb : (Scheme.Modules.pullback b).obj Mb ≅ N)
    (e : (Scheme.Modules.pullback c).obj N ≅ P)
    (ea' : (Scheme.Modules.pullback a').obj Ma ≅ P)
    (eb' : (Scheme.Modules.pullback b').obj Mb ≅ P)
    (hea : (Scheme.Modules.pullback c).map ea.hom ≫ e.hom =
      compHom c a a' ha Ma ≫ ea'.hom)
    (heb : (Scheme.Modules.pullback c).map eb.hom ≫ e.hom =
      compHom c b b' hb Mb ≫ eb'.hom) :
    (Scheme.Modules.pullback t).map (transition q a b f g hf hg ea eb).hom ≫
        compHom t g s hs Mb ≫ (normalize r b' s hs' eb').hom =
      compHom t f p hp Ma ≫ (normalize r a' p hp' ea').hom := by
  rw [← normalize_refine t q r c b g b' s ht hg hb hs hs' eb e eb' heb]
  simp only [transition, Iso.trans_hom, Iso.symm_hom, Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc (Scheme.Modules.pullback t) (normalize q b g hg eb).inv,
    Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp]
  exact normalize_refine t q r c a f a' p ht hf ha hp hp' ea e ea' hea

/-- Canonical changes of the outer two maps preserve a fixed normalization. -/
lemma square_normalize {W V V' A L : Scheme.{u}}
    (t : W ⟶ V) (s : W ⟶ V') (f : V ⟶ A) (g : V' ⟶ A)
    (p : W ⟶ A) (q : W ⟶ L) (a : L ⟶ A)
    (h : t ≫ f = s ≫ g) (hp : t ≫ f = p) (hp' : s ≫ g = p)
    (ha : q ≫ a = p) {M : A.Modules} {N : L.Modules}
    (e : (Scheme.Modules.pullback a).obj M ≅ N) :
    (squarePullbackIso g t s f h M).hom ≫
        compHom s g p hp' M ≫ (normalize q a p ha e).hom =
      compHom t f p hp M ≫ (normalize q a p ha e).hom := by
  rw [reassoc_of% (CommonSourceCocycle.square_normalize g t s f h M p hp')]

end Langlands.Scheme.Modules.RefinedPullbackComparison
