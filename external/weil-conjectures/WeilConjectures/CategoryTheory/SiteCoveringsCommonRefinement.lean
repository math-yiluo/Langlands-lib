/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.Hypercover.Zero

/-!
# Common refinements of coverings of a site

Source: Stacks Project, Sites, Lemma 7.10.5 (Tag 00W6) and its proof
(blueprint: lem-weil-pbc-site-coverings-common-refinement).
-/

@[expose] public section

universe u w w' t

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Precoverage

/-- Any choice of the pairwise fibre products gives a covering, and the specified projections
are refinement morphisms with the two coordinate index maps. Source: Stacks Project,
Sites, Lemma 7.10.5 (Tag 00W6)
(blueprint: lem-weil-pbc-site-coverings-common-refinement).

Proof: Apply site axiom (iii) (def-weil-pbc-sites-and-cohomology) to the second covering
along each member of the first, using the given pullback squares. The resulting families
cover each `E.X i`. Apply axiom (ii) to compose these families with `E`. Reindex the sigma
index type by its equivalence with the product to obtain the displayed covering presieve.
The maps `q` and `p`, with index maps `Prod.fst` and `Prod.snd`, satisfy the commuting
triangles by the structure-map definition and the pullback-square equation, respectively.
These are precisely morphisms of coverings over the identity as in
 def-weil-pbc-site-plus-construction (b). -/
theorem siteCoverings_common_refinement {C : Type u} [SmallCategory C]
    (J : Precoverage C) [J.HasIsos] [J.IsStableUnderComposition]
    [J.IsStableUnderBaseChange] [J.HasPullbacks] {U : C}
    (E : ZeroHypercover.{w} J U) (F : ZeroHypercover.{w'} J U)
    (W : E.I₀ × F.I₀ → C)
    (q : ∀ ij : E.I₀ × F.I₀, W ij ⟶ E.X ij.1)
    (p : ∀ ij : E.I₀ × F.I₀, W ij ⟶ F.X ij.2)
    (h : ∀ ij : E.I₀ × F.I₀, IsPullback (p ij) (q ij) (F.f ij.2) (E.f ij.1)) :
    Presieve.ofArrows W (fun ij => q ij ≫ E.f ij.1) ∈ J U ∧
    (∃ r : PreZeroHypercover.Hom
      { I₀ := E.I₀ × F.I₀, X := W, f := fun ij => q ij ≫ E.f ij.1 }
      E.toPreZeroHypercover, r.s₀ = _root_.Prod.fst ∧ HEq r.h₀ q) ∧
    (∃ r : PreZeroHypercover.Hom
      { I₀ := E.I₀ × F.I₀, X := W, f := fun ij => q ij ≫ E.f ij.1 }
      F.toPreZeroHypercover, r.s₀ = _root_.Prod.snd ∧ HEq r.h₀ p) := by
  let G : PreZeroHypercover U :=
    { I₀ := E.I₀ × F.I₀
      X := W
      f := fun ij => q ij ≫ E.f ij.1 }
  let e : G ≅ (E.inter F).toPreZeroHypercover :=
    PreZeroHypercover.isoMk (Equiv.refl _) (fun ij ↦ (h ij).flip.isoPullback) (fun ij ↦ by
      change (h ij).flip.isoPullback.hom ≫ pullback.fst (E.f ij.1) (F.f ij.2) ≫ E.f ij.1 =
        q ij ≫ E.f ij.1
      rw [← Category.assoc, (h ij).flip.isoPullback_hom_fst])
  have hG : G.presieve₀ ∈ J U := by
    exact (PreZeroHypercover.mem_iff_of_iso (K := J) e).mpr (E.inter F).mem₀
  refine ⟨hG, ?_, ?_⟩
  · let r : G.Hom E.toPreZeroHypercover :=
      { s₀ := _root_.Prod.fst
        h₀ := q }
    exact ⟨r, rfl, HEq.rfl⟩
  · let r : G.Hom F.toPreZeroHypercover :=
      { s₀ := _root_.Prod.snd
        h₀ := p
        w₀ := fun ij ↦ (h ij).w }
    exact ⟨r, rfl, HEq.rfl⟩

/-- Any finite family of coverings of an object has a common refinement.
Source: Stacks Project, Sites, Lemma 7.10.5 (Tag 00W6), finite iteration
(blueprint: lem-weil-pbc-site-coverings-common-refinement).

Proof: Induct on the cardinality of the finite family. For the empty family use the
singleton identity covering, which is a covering by axiom (i) of
 def-weil-pbc-sites-and-cohomology. At the induction step use the binary common-refinement
construction above to refine the previous common refinement and the new covering.
Compose its projection to the previous refinement with each previously obtained
refinement morphism (def-weil-pbc-site-plus-construction (b)); its other projection refines
the new covering. Product index types stay in the same universe under finite iteration. -/
theorem siteCoverings_finite_common_refinement {C : Type u} [SmallCategory C]
    (J : Precoverage C) [J.HasIsos] [J.IsStableUnderComposition]
    [J.IsStableUnderBaseChange] [J.HasPullbacks] {U : C}
    (K : Type t) [Finite K] (E : K → ZeroHypercover.{w} J U) :
    ∃ W : ZeroHypercover.{w} J U, ∀ k : K, Nonempty (ZeroHypercover.Hom J W (E k)) := by
  classical
  induction K using Finite.induction_empty_option with
  | @of_equiv K₁ K₂ e ih =>
      obtain ⟨W, hW⟩ := ih (E := E ∘ e)
      exact ⟨W, fun k ↦ by simpa using hW (e.symm k)⟩
  | h_empty =>
      let W : ZeroHypercover.{w} J U :=
        ZeroHypercover.singleton (𝟙 U) (J.mem_coverings_of_isIso (𝟙 U))
      exact ⟨W, fun k ↦ k.elim⟩
  | @h_option K₁ _ ih =>
      obtain ⟨W, hW⟩ := ih (E := fun k ↦ E (.some k))
      let V := W.inter (E .none)
      refine ⟨V, ?_⟩
      intro k
      cases k with
      | none =>
          exact ⟨PreZeroHypercover.interSnd W.toPreZeroHypercover
            (E .none).toPreZeroHypercover⟩
      | some k =>
          let a : ZeroHypercover.Hom J V W :=
            PreZeroHypercover.interFst W.toPreZeroHypercover
              (E .none).toPreZeroHypercover
          exact ⟨PreZeroHypercover.Hom.comp a (hW k).some⟩

end CategoryTheory.Precoverage
