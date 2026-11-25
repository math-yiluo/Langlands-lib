/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FiberDegreeBound
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Topology.Basic
import WeilConjectures.AlgebraicGeometry.FlatFpLqfMaximalDegreeLocus
import WeilConjectures.AlgebraicGeometry.FiniteFiberDegreeBaseChange
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.AlgebraicGeometry.SeparatedLqfBaseChange

/-!
# Stratification of flat finitely presented locally quasi-finite morphisms

Source: Stacks Project, More on Morphisms, Lemma Tag 07RY
(blueprint: lem-weil-pbc-flat-fp-lqf-bounded-stratification).

As in `WeilConjectures.AlgebraicGeometry.FlatQuasiFiniteStratification`, the closed filtration is
indexed from zero: `Z 0` is the paper's `Z_{-1} = ∅` and `Z (r + 1)` is the paper's `Z_r`,
so the degree-`r` stratum is `Z (r + 1) \ Z r`, written out in place. The bound `n` is the
one supplied by the hypothesis `BoundsFiberDegrees f n`, and `Z (n + 1) = Set.univ`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Hom

private theorem isClosed_fiber_degree_le (n : ℕ) {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [LocallyOfFinitePresentation f] [IsSeparated f]
    (h_lqf : IsLocallyQuasiFinite f) (hn : BoundsFiberDegrees f n) (r : ℕ) :
    IsClosed {s : S | (f.fiberToSpecResidueField s).finrankΓ ≤ r} := by
  induction n generalizing X S with
  | zero =>
    have heq : {s : S | (f.fiberToSpecResidueField s).finrankΓ ≤ r} = Set.univ := by
      ext s
      simp only [Set.mem_ofPred, Set.mem_univ, iff_true]
      exact (hn s).2.trans (Nat.zero_le r)
    rw [heq]
    exact isClosed_univ
  | succ n ih =>
    by_cases hnr : n + 1 ≤ r
    · have heq : {s : S | (f.fiberToSpecResidueField s).finrankΓ ≤ r} = Set.univ := by
        ext s
        simp only [Set.mem_ofPred, Set.mem_univ, iff_true]
        exact (hn s).2.trans hnr
      rw [heq]
      exact isClosed_univ
    · obtain ⟨U, hU, _⟩ :=
        exists_isFinite_morphismRestrict_maximal_fiber_degree f h_lqf (n + 1) hn
      have hC : IsClosed {s : S | (f.fiberToSpecResidueField s).finrankΓ ≤ n} := by
        have heq : {s : S | (f.fiberToSpecResidueField s).finrankΓ ≤ n} =
            (U : Set S)ᶜ := by
          ext s
          change (f.fiberToSpecResidueField s).finrankΓ ≤ n ↔ ¬ s ∈ U
          rw [hU s]
          have hs := (hn s).2
          omega
        rw [heq]
        exact U.isOpen.isClosed_compl
      let C : TopologicalSpace.Closeds S := ⟨_, hC⟩
      let I := Scheme.IdealSheafData.vanishingIdeal C
      let i := I.subschemeι
      have hi := Scheme.IdealSheafData.reduced_induced_closed_subscheme S C
      have : IsClosedImmersion i := hi.2.2.1
      have hrange : Set.range i = (C : Set S) := hi.2.2.2.2.2.1
      let f' := pullback.snd f i
      have hlqf' : IsLocallyQuasiFinite f' := (separated_lqf_base_change f i).2 h_lqf
      have hdegree (t : I.subscheme) :
          (f'.fiberToSpecResidueField t).finrankΓ =
            (f.fiberToSpecResidueField (i t)).finrankΓ :=
        (finite_fiber_degree_pullback f i t (hn (i t)).1).2
      have hn' : BoundsFiberDegrees f' n := by
        intro t
        refine ⟨(finite_fiber_degree_pullback f i t (hn (i t)).1).1, ?_⟩
        rw [hdegree]
        have ht : i t ∈ (C : Set S) := by
          rw [← hrange]
          exact Set.mem_range_self t
        exact ht
      have hclosed := ih f' hlqf' hn'
      have himage : i '' {t | (f'.fiberToSpecResidueField t).finrankΓ ≤ r} =
          {s : S | (f.fiberToSpecResidueField s).finrankΓ ≤ r} := by
        ext s
        constructor
        · rintro ⟨t, ht, rfl⟩
          simpa only [Set.mem_ofPred, hdegree] using ht
        · intro hs
          have hsC : s ∈ (C : Set S) := by
            change (f.fiberToSpecResidueField s).finrankΓ ≤ n
            have hs' : (f.fiberToSpecResidueField s).finrankΓ ≤ r := hs
            omega
          rw [← hrange] at hsC
          obtain ⟨t, rfl⟩ := hsC
          exact ⟨t, by simpa only [Set.mem_ofPred, hdegree] using hs, rfl⟩
      rw [← himage]
      exact i.isClosedEmbedding.isClosedMap _ hclosed

/-- Flat, locally finitely presented, separated, locally quasi-finite morphisms with universally
bounded fibres are finite locally free on a finite stratification (Stacks, Tag 07RY;
(blueprint: lem-weil-pbc-flat-fp-lqf-bounded-stratification).

Proof (Stacks Tag 07RY, following the ten steps of the blueprint node):
1. Choose a bound on fibre degrees. Base change preserves flatness, local finite presentation,
   separatedness and local quasi-finiteness, and preserves each fibre degree
   (`lem-weil-pbc-flat-morphism-base-change`, `lem-weil-pbc-qcqs-morphism-permanence`,
   `lem-weil-pbc-separated-lqf-base-change`, `lem-weil-pbc-fibre-degree-base-change`).
2. For a point of maximal degree `m`, use an elementary étale neighbourhood to split the
   pullback into a finite part `V` and an open part `W` with empty fibre at that point
   (`lem-weil-pbc-finite-closed-map-finite-fibres`, `def-pc-scheme-fibre`,
   `lem-weil-pbc-etale-splits-off-quasi-finite-part`).
3. The finite part is flat and locally of finite presentation by restriction to an open,
   hence finite locally free (`def-pc-finite-locally-free`).
4. Shrink the neighbourhood so that `V` has constant degree. Its degree is `m` because the
   fibre of `W` at the chosen point is empty (
   `lem-weil-pbc-finite-locally-free-degree-locally-constant`,
   `lem-weil-pbc-open-preimage-fibre-product`,
   `definition-torsion-sheaves--3`, `lem-weil-pbc-fibre-degree-base-change`).
5. Additivity of degrees on the disjoint open parts and the bound `m` force every fibre of
   `W` to be empty. Thus `W` is empty and the image of the neighbourhood is in the degree-`m`
   locus. Étale maps are open, so this locus is open (`lem-weil-pbc-etale-morphism-open-map`).
6. Factor the neighbourhood maps through that open locus and descend finite local freeness
   of degree `m` along this étale cover (`lem-weil-pbc-morphism-factors-through-open-subscheme`,
   `lem-weil-pbc-finite-locally-free-degree-etale-descent`). This proves the maximal-degree claim.
7. Put `Z (r + 1) = {s | the fibre degree at s is at most r}` and `Z 0 = ∅`. Induct on the
   bound: for bound zero these are the whole base; otherwise the complement of the
   maximal-degree locus is closed.
   Give it the reduced induced closed subscheme structure and apply induction to the pullback,
   whose bound is one smaller (`lem-weil-pbc-reduced-induced-closed-subscheme`,
   `lem-weil-pbc-fibre-degree-base-change`). The closed immersion makes all `Z r` closed in `S`.
8. Successive differences are precisely the degree loci, hence disjoint and cover `S`;
   degree loci above the bound `n` are empty since `Z r = Set.univ` for `r ≥ n + 1`.
9. If a base change is finite locally free of degree `r`, fibre-degree invariance puts every
   image point in the degree-`r` stratum (`lem-weil-pbc-fibre-degree-base-change`).
10. Conversely, if the image lies in that stratum, every fibre of the base change has degree
    `r`. Apply the maximal-degree claim to that base change with bound `r` to obtain finite
    local freeness of degree `r`, including the empty-base case.
-/
theorem exists_flat_fp_lqf_bounded_stratification {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [LocallyOfFinitePresentation f] [IsSeparated f]
    (h_lqf : IsLocallyQuasiFinite f) (n : ℕ) (hn : BoundsFiberDegrees f n) :
    ∃ Z : ℕ → Set S,
      Z 0 = ∅ ∧ (∀ r : ℕ, IsClosed (Z r)) ∧ Monotone Z ∧ Z (n + 1) = Set.univ ∧
      Pairwise (fun r t : ℕ => Disjoint (Z (r + 1) \ Z r) (Z (t + 1) \ Z t)) ∧
      (⋃ r : ℕ, Z (r + 1) \ Z r) = Set.univ ∧
      (∀ (T : Scheme.{u}) (g : T ⟶ S) (r : ℕ),
        (pullback.snd f g).IsFiniteLocallyFreeOfDegree r ↔ Set.range g ⊆ Z (r + 1) \ Z r) := by
  classical
  let δ : S → ℕ := fun s ↦ (f.fiberToSpecResidueField s).finrankΓ
  let Z : ℕ → Set S
    | 0 => ∅
    | r + 1 => {s | δ s ≤ r}
  have hstratum (r : ℕ) : Z (r + 1) \ Z r = {s | δ s = r} := by
    ext s
    cases r with
    | zero => simp [Z]
    | succ r =>
      simp only [Z, Set.mem_sdiff, Set.mem_ofPred]
      omega
  refine ⟨Z, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r
    cases r with
    | zero => exact isClosed_empty
    | succ r => exact isClosed_fiber_degree_le n f h_lqf hn r
  · intro a b hab
    cases a with
    | zero => exact Set.empty_subset _
    | succ a =>
      cases b with
      | zero => omega
      | succ b =>
        intro s hs
        exact Nat.le_trans hs (by omega)
  · ext s
    simp only [Z, Set.mem_ofPred, Set.mem_univ, iff_true]
    exact (hn s).2
  · intro r t hrt
    rw [hstratum r, hstratum t, Set.disjoint_left]
    intro s hs ht
    exact hrt (hs.symm.trans ht)
  · simp_rw [hstratum]
    ext s
    simp only [Set.mem_iUnion, Set.mem_ofPred, Set.mem_univ, iff_true]
    exact ⟨δ s, rfl⟩
  · intro T g r
    rw [hstratum]
    constructor
    · intro h
      have := h
      rintro s ⟨t, rfl⟩
      have hdeg := (finite_fiber_degree_pullback f g t (hn (g t)).1).2
      change (f.fiberToSpecResidueField (g t)).finrankΓ = r
      rw [← hdeg]
      exact h.fiberDegree_eq t
    · intro h
      let f' := pullback.snd f g
      have hlqf' : IsLocallyQuasiFinite f' := (separated_lqf_base_change f g).2 h_lqf
      have hdeg (t : T) : (f'.fiberToSpecResidueField t).finrankΓ = r := by
        rw [(finite_fiber_degree_pullback f g t (hn (g t)).1).2]
        exact h (Set.mem_range_self t)
      have hr : BoundsFiberDegrees f' r := fun t ↦
        ⟨(finite_fiber_degree_pullback f g t (hn (g t)).1).1, (hdeg t).le⟩
      obtain ⟨U, hU, hfinite⟩ :=
        exists_isFinite_morphismRestrict_maximal_fiber_degree f' hlqf' r hr
      have : IsFinite f' :=
        IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict (P := @IsFinite)
          (fun t ↦ ⟨U, (hU t).mpr (hdeg t), hfinite⟩)
      have : f'.IsFiniteLocallyFree := {}
      exact { fiberDegree_eq := fun t ↦ hdeg t }

end AlgebraicGeometry.Scheme.Hom
