/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.ArrowsFunctor
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Functor.KanExtension.Basic
public import Mathlib.CategoryTheory.Filtered.Basic
import WeilConjectures.CategoryTheory.ColimitSiteFiniteKanArrowLift
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import Mathlib.CategoryTheory.Limits.Types.Colimits

/-! # Equality of Kan units at one stage

Source: Stacks Project, Sites, Tag 0A35 (lemma-compute-pullback-to-limit),
independence of presentations in the section construction.
(blueprint: lem-weil-pbc-colimit-site-kan-unit-relations).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- An equality in the relation-generated colimit uses only finitely many objects
and arrows. Any family respecting these arrows identifies the two endpoints. -/
private theorem finite_colimit_relation_support
    {D : Type u} [SmallCategory D] (G : D ⥤ Type u)
    {x y : Σ d, G.obj d} (h : Relation.EqvGen G.ColimitTypeRel x y) :
    ∃ (S : Finset D) (T : Finset (Σ p q : D, p ⟶ q))
      (hx : x.1 ∈ S) (hy : y.1 ∈ S),
      ∀ (Z : Type u) (e : ∀ p : S, G.obj p.val → Z),
        (∀ (p q : S) (f : p.val ⟶ q.val), ⟨p.val, q.val, f⟩ ∈ T →
          ∀ a, e q (G.map f a) = e p a) →
        e ⟨x.1, hx⟩ x.2 = e ⟨y.1, hy⟩ y.2 := by
  classical
  induction h with
  | rel x y h =>
    obtain ⟨f, hf⟩ := h
    refine ⟨{x.1, y.1}, {⟨x.1, y.1, f⟩}, by simp, by simp, ?_⟩
    intro Z e he
    rw [hf]
    exact (he ⟨x.1, by simp⟩ ⟨y.1, by simp⟩ f (by simp) x.2).symm
  | refl x =>
    exact ⟨{x.1}, ∅, by simp, by simp, fun _ _ _ ↦ rfl⟩
  | symm x y _ ih =>
    obtain ⟨S, T, hx, hy, he⟩ := ih
    exact ⟨S, T, hy, hx, fun Z e hn ↦ (he Z e hn).symm⟩
  | trans x y z _ _ ih₁ ih₂ =>
    obtain ⟨S₁, T₁, hx, hy₁, he₁⟩ := ih₁
    obtain ⟨S₂, T₂, hy₂, hz, he₂⟩ := ih₂
    refine ⟨S₁ ∪ S₂, T₁ ∪ T₂, Finset.mem_union_left _ hx,
      Finset.mem_union_right _ hz, ?_⟩
    intro Z e hn
    let e₁ (p : S₁) := e ⟨p.val, Finset.mem_union_left _ p.property⟩
    let e₂ (p : S₂) := e ⟨p.val, Finset.mem_union_right _ p.property⟩
    have h₁ := he₁ Z e₁ (fun p q f hf a ↦ hn
      ⟨p.val, Finset.mem_union_left _ p.property⟩
      ⟨q.val, Finset.mem_union_left _ q.property⟩ f
      (Finset.mem_union_left _ hf) a)
    have h₂ := he₂ Z e₂ (fun p q f hf a ↦ hn
      ⟨p.val, Finset.mem_union_right _ p.property⟩
      ⟨q.val, Finset.mem_union_right _ q.property⟩ f
      (Finset.mem_union_right _ hf) a)
    exact h₁.trans h₂

/-- Source: Stacks Project, Sites, Tag 0A35 (lemma-compute-pullback-to-limit),
section construction, independence of the presentation and restriction arrows.
(blueprint: lem-weil-pbc-colimit-site-kan-unit-relations).

Proof: Compute the value of the left Kan extension K by the set colimit
on structured arrows. The two unit generators have the same stage object and
identity arrow. Their equality is witnessed by a finite zigzag of generating
Kan relations. Lift all arrows in this zigzag to a common later category,
using surjectivity of the arrow colimit. The object-colimit equality criterion
aligns their endpoints with the transported stage objects. Refine once more
so the arrow-colimit equality criterion enforces all triangles and identifies
the two endpoint arrows with identities. Equalize the finitely many competing
maps from i and t.right, obtaining one morphism b in Under i.

Choose one b : t -> r at the common refinement. Map each generator (W, f, s)
to theta_b(s) restricted along its lifted arrow g : F(b.right)(U) -> F(b.right)(W).
A generating relation associated to h : W -> W' identifies the restriction
of s' along h with s' at W'. The lifted arrows satisfy
g' = g followed by F(b.right)(h). Naturality gives
theta_b(A_t(h.op)(s')) = A_r(F(b.right)(h).op)(theta_b(s')).
Restriction along g therefore has the same value as restriction along g'.
The reversed relation gives the reversed equality, and reflexive relations
are immediate.
Naturality of theta and the lifted triangles identify the images of each Kan
relation. Induction along the zigzag therefore equates the endpoint sections.
The identity endpoint arrows identify the two endpoint images with theta_b(x)
and theta_b(x'). No coherence between different theta maps is needed, since
all generators use the same b. No outer presheaf-colimit equality, sheaf
condition, or section diagram D is used in this argument.
-/
theorem raw_section_kan_unit_relations
    (J : Type u) [SmallCategory J] [IsFiltered J] (F : J ⥤ Cat.{u, u})
    (V : Cocone F)
    (hobjects : IsColimit (Cat.objects.mapCocone V))
    (harrows : IsColimit (Cat.arrows.mapCocone V))
    (i : J) (t : Under i)
    (A : ∀ r : Under i, (F.obj r.right)ᵒᵖ ⥤ Type u)
    (θ : ∀ (r : Under i) (b : t ⟶ r),
      A t ⟶ (F.map b.right).toFunctor.op ⋙ A r)
    (K : V.ptᵒᵖ ⥤ Type u)
    (β : A t ⟶ (V.ι.app t.right).toFunctor.op ⋙ K)
    (hβ : K.IsLeftKanExtension β)
    (U : F.obj t.right) :
    ∀ (x x' : (A t).obj (op U)), β.app (op U) x = β.app (op U) x' →
      ∃ (r : Under i) (b : t ⟶ r),
        (θ r b).app (op U) x = (θ r b).app (op U) x' := by
  classical
  let : K.IsLeftKanExtension β := hβ
  let L := (V.ι.app t.right).toFunctor.op
  let Y := L.obj (op U)
  let D := CostructuredArrow L Y
  let G : D ⥤ Type u := CostructuredArrow.proj L Y ⋙ A t
  let p : D := CostructuredArrow.mk (𝟙 Y)
  let c := (Functor.LeftExtension.mk K β).coconeAt Y
  let hc := Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension K β Y
  intro x x' hxx'
  have hq : G.ιColimitType p x = G.ιColimitType p x' := by
    apply (Types.isColimit_iff_coconeTypesIsColimit c).mp ⟨hc⟩ |>.bijective.1
    change K.map (𝟙 Y) (β.app (op U) x) = K.map (𝟙 Y) (β.app (op U) x')
    rw [K.map_id]
    exact hxx'
  have hr := (G.ιColimitType_eq_iff (j := p) (j' := p) x x').mp hq
  obtain ⟨S, T, hx, hx', he⟩ := finite_colimit_relation_support G hr
  obtain ⟨r, b, g, hg, hgid⟩ :=
    colimit_site_finite_kan_arrow_lift J F V hobjects harrows i t U S T hx
  let e (q : S) (s : G.obj q.val) :
      (A r).obj ((F.map b.right).toFunctor.op.obj (op U)) :=
    (A r).map (g q).op ((θ r b).app q.val.left s)
  have hn (q q' : S) (f : q.val ⟶ q'.val) (hf : ⟨q.val, q'.val, f⟩ ∈ T)
      (s : G.obj q.val) : e q' (G.map f s) = e q s := by
    change (A t).obj q.val.left at s
    change (A r).map (g q').op
      ((θ r b).app q'.val.left ((A t).map f.left s)) =
      (A r).map (g q).op ((θ r b).app q.val.left s)
    have hθ := ConcreteCategory.congr_hom ((θ r b).naturality f.left) s
    change (θ r b).app q'.val.left ((A t).map f.left s) =
      (A r).map ((F.map b.right).toFunctor.op.map f.left)
        ((θ r b).app q.val.left s) at hθ
    rw [hθ]
    have hm := ConcreteCategory.congr_hom
      ((A r).map_comp ((F.map b.right).toFunctor.op.map f.left) (g q').op)
      ((θ r b).app q.val.left s)
    refine hm.symm.trans ?_
    have hh : (F.map b.right).toFunctor.op.map f.left ≫ (g q').op = (g q).op := by
      exact congrArg Quiver.Hom.op (hg q q' f hf)
    rw [hh]
    rfl
  have h := he _ e hn
  refine ⟨r, b, ?_⟩
  change (A r).map (g ⟨p, hx⟩).op ((θ r b).app (op U) x) =
    (A r).map (g ⟨p, hx'⟩).op ((θ r b).app (op U) x') at h
  have hid : g ⟨p, hx⟩ = 𝟙 _ := hgid
  rw [hid, op_id] at h
  rw [(A r).map_id (op ((F.map b.right).toFunctor.obj U))] at h
  exact h


end CategoryTheory
