/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.FilteredTwoColimitModel
public import Mathlib.CategoryTheory.Equivalence

/-! # The comparison characterizes a filtered 2-colimit

For a coherent cocone `c` on a directed system of categories, the comparison functor from the
explicit model `FilteredTwoColimit.Object c` is essentially surjective, full, or faithful exactly
when the cocone satisfies the object, Hom-surjectivity, or Hom-injectivity condition of
`CategoryCocone.IsFilteredTwoColimit`; hence the cocone is a filtered 2-colimit if and only if the
comparison is an equivalence.

(blueprint: proposition-dctf-x-qbar-2-colimit--1).
-/

@[expose] public section

universe w u v u' v'

namespace CategoryTheory.FilteredTwoColimit

/-- The three finite-stage conditions characterize the corresponding properties of the canonical
comparison functor, and their conjunction characterizes its being an equivalence.

Stacks
04AX and 02C3 (blueprint: proposition-dctf-x-qbar-2-colimit--1).

Proof plan:
1. The model's objects are pairs (i,x), whose comparison images are Phi_i(x). Thus essential
surjectivity is precisely Obj; invert the witnessing isomorphism if necessary.
2. For a pair of objects the common-stage preorder is small, nonempty and filtered. By the
filtered set-colimit representative lemma, each arrow is [k,g]. Its comparison image is theta_jk
composed with Phi_k(g) and theta_ik inverse. Hence fullness is precisely Hom-surj.
3. Under Hom-inj, move two representatives with equal images to one stage, cancel the outer
comparison isomorphisms, and apply Hom-inj there. Conjugate the resulting equality by the tau
components. The filtered set-colimit equality criterion makes the original classes equal.
4. Conversely, faithfulness applied to [k,g] and [k,g'] gives equality of classes when Phi_k(g)
equals Phi_k(g'). Normalization identifies their images with these arrows. The set-colimit
criterion supplies a later stage where their transitions agree, and tau_kkn normalization turns
this into equality after T_kn. This is Hom-inj.
5. The three clauses and the fully faithful, essentially surjective criterion give an equivalence
via Functor.asEquivalence. Conversely a quasi-inverse supplies essential surjectivity and bijective
Hom maps (Equivalence.fullyFaithfulFunctor); steps 1--4 recover the three cocone conditions. -/
theorem comparison_characterization
    {I : Type w} [Preorder I] [IsDirected I (· ≤ ·)]
    {C : I → Type u} [∀ i : I, Category.{v} (C i)]
    {D : Type u'} [Category.{v'} D] (c : CoherentCategoryCocone (C := C) (D := D)) :
    ((comparison c).EssSurj ↔ c.toCategoryCocone.EssSurjObj) ∧
    ((comparison c).Full ↔ c.toCategoryCocone.HomSurj) ∧
    ((comparison c).Faithful ↔ c.toCategoryCocone.HomInj) ∧
    (c.toCategoryCocone.IsFilteredTwoColimit ↔ (comparison c).IsEquivalence) := by
  have map_class {a b : Object c} (k : CommonStage a.1 b.1) (g : HomAt c a b k) :
      (comparison c).map (homClass c k g) =
        (c.iso k.2.1).inv.app a.2 ≫ (c.Φ k.1).map g ≫ (c.iso k.2.2).hom.app b.2 := rfl
  have hobj : (comparison c).EssSurj ↔ c.toCategoryCocone.EssSurjObj := by
    constructor
    · intro h d
      obtain ⟨⟨i, x⟩, e⟩ := h.mem_essImage d
      exact ⟨i, x, e⟩
    · intro h
      constructor
      intro d
      obtain ⟨i, x, e⟩ := h d
      exact ⟨⟨i, x⟩, e⟩
  have hfull : (comparison c).Full ↔ c.toCategoryCocone.HomSurj := by
    constructor
    · intro h i j x y f
      obtain ⟨g, hg⟩ := h.map_surjective (X := ⟨i, x⟩) (Y := ⟨j, y⟩) f
      obtain ⟨k, g, rfl⟩ :=
        (homDiagram c ⟨i, x⟩ ⟨j, y⟩).ιColimitType_jointly_surjective g
      exact ⟨k.1, k.2.1, k.2.2, g, hg.symm⟩
    · intro h
      constructor
      intro a b f
      obtain ⟨k, hi, hj, g, hg⟩ := h a.1 b.1 a.2 b.2 f
      exact ⟨homClass c ⟨k, hi, hj⟩ g, hg.symm⟩
  have hfaithful : (comparison c).Faithful ↔ c.toCategoryCocone.HomInj := by
    constructor
    · intro h k x y g g' hg
      let a : Object c := ⟨k, x⟩
      let b : Object c := ⟨k, y⟩
      let kk : CommonStage k k := ⟨k, le_refl k, le_refl k⟩
      have image (f : x ⟶ y) :
          (comparison c).map
              (homClass c (a := a) (b := b) kk ((c.T (le_refl k)).map f)) =
            (c.Φ k).map f := by
        exact NatIso.naturality_1 (c.iso (le_refl k)) f
      have heq : homClass c (a := a) (b := b) kk ((c.T (le_refl k)).map g) =
          homClass c (a := a) (b := b) kk ((c.T (le_refl k)).map g') := by
        apply h.map_injective
        rw [image g, image g', hg]
      obtain ⟨m, hm, hm', he⟩ :=
        (homClass_eq_iff c (a := a) (b := b) kk kk _ _).mp heq
      refine ⟨m.1, hm, ?_⟩
      have transition (f : x ⟶ y) :
          homTransition c (a := a) (b := b) (k := kk) (l := m) hm
              ((c.T (le_refl k)).map f) = (c.T hm).map f := by
        exact NatIso.naturality_1 (c.tau (le_refl k) hm) f
      simpa only [transition] using he
    · intro h
      constructor
      intro a b f g hfg
      obtain ⟨k, f, rfl⟩ := (homDiagram c a b).ιColimitType_jointly_surjective f
      obtain ⟨l, g, rfl⟩ := (homDiagram c a b).ιColimitType_jointly_surjective g
      obtain ⟨m, hkm, hlm⟩ := exists_ge_ge k.1 l.1
      let mm : CommonStage a.1 b.1 := ⟨m, k.2.1.trans hkm, k.2.2.trans hkm⟩
      let f' : HomAt c a b mm := homTransition c hkm f
      let g' : HomAt c a b mm := homTransition c hlm g
      have hf : homClass c mm f' = homClass c k f := homClass_transition c hkm f
      have hg : homClass c mm g' = homClass c l g := homClass_transition c hlm g
      have he : (c.Φ m).map f' = (c.Φ m).map g' := by
        have he : (comparison c).map (homClass c mm f') =
            (comparison c).map (homClass c mm g') := by
          rw [hf, hg]
          exact hfg
        simpa only [map_class, cancel_epi, cancel_mono] using he
      obtain ⟨n, hmn, hn⟩ := h m _ _ f' g' he
      let nn : CommonStage a.1 b.1 := ⟨n, mm.2.1.trans hmn, mm.2.2.trans hmn⟩
      have heq : homClass c mm f' = homClass c mm g' := by
        apply (homClass_eq_iff c mm mm f' g').mpr
        refine ⟨nn, hmn, hmn, ?_⟩
        dsimp only [homTransition]
        rw [hn]
      exact hf.symm.trans (heq.trans hg)
  refine ⟨hobj, hfull, hfaithful, ?_⟩
  constructor
  · intro h
    exact ⟨hfaithful.mpr h.homInj, hfull.mpr h.homSurj, hobj.mpr h.essSurjObj⟩
  · intro h
    exact ⟨hobj.mp h.essSurj, hfull.mp h.full, hfaithful.mp h.faithful⟩

end CategoryTheory.FilteredTwoColimit
