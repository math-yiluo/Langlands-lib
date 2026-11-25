module

public import Mathlib.Order.SuccPred.ENat
public import Mathlib.Topology.GDelta.Basic
public import Mathlib.Topology.NoetherianSpace
public import StacksFrontier.Topology.Dimension.Krull

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# A nowhere dense closed subset has strictly smaller dimension

In a Noetherian space `X`, a closed subset `S` with empty interior misses every irreducible
component: an irreducible component of a Noetherian space contains a nonempty open subset of
`X` (`TopologicalSpace.NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent`,
Stacks 0052 (3)), so a component inside `S` would make `interior S` nonempty. Hence a maximal
chain of irreducible closed subsets of `S`, read in `X`, can always be extended upwards by one
step, and `dim S` is smaller than `dim X` by at least one.

## Main results

* `IsClosed.isNowhereDense_iff_forall_irreducibleComponents_not_subset`: for a closed subset of
  a Noetherian space, nowhere density is exactly missing every irreducible component. This is
  the criterion in which the hypothesis is checkable.
* `IsNowhereDense.not_isMax_of_subset`: an irreducible closed subset of a nowhere dense closed
  set is never maximal among the irreducible closed subsets of the ambient Noetherian space.
* `IsNowhereDense.topologicalKrullDim_add_one_le`: `dim S + 1 ≤ dim X`. This is the sharp
  statement, and needs no finiteness or nonemptiness hypothesis, by the conventions
  `dim ∅ = -∞` and `-∞ + 1 = -∞`.
* `IsNowhereDense.topologicalKrullDim_lt`: the strict inequality `dim S < dim X`, for `X`
  nonempty and finite-dimensional. Both side conditions are necessary: for `X` empty both
  sides are `-∞`, and for `dim X = ∞` a nowhere dense closed subset can again have
  dimension `∞`.
* `IsNowhereDense.toNat_unbotD_topologicalKrullDim_lt`: the same strict inequality between the
  two dimensions read as natural numbers, which is the form a dimension-descending induction
  consumes.
* `IsNowhereDense.topologicalKrullDim_le_of_le_natCast_succ` and
  `IsNowhereDense.topologicalKrullDim_nonpos_of_le_one`: the bounded forms, which need no side
  condition because the bound on `dim X` supplies the finite-dimensionality.
* `toNat_unbotD_topologicalKrullDim_lt_of_isNowhereDense_subspace`: the relative form, between
  two subsets `A ⊆ Y` of a common ambient space with `A` nowhere dense in `Y`, using
  `topologicalKrullDim_preimage_val` (in `StacksFrontier.Topology.Dimension.Krull`) to read the
  dimension of `A` in either ambient space.
* `isNowhereDense_preimage_val_iff_forall_irreducibleComponents`: nowhere density *inside a
  subspace* `Y`, as a condition on the irreducible components of `Y`. This is the form in which
  the relative hypothesis of the previous statement is checkable, and the form that makes the
  gap between it and absolute nowhere density visible: the components of `Y` are not the
  components of the ambient space, so a set nowhere dense in the ambient space can contain one
  of them.
* `topologicalKrullDim_univ`: the subspace `Set.univ` has the dimension of the whole space.
  Together with the previous statement this is the one case in which absolute nowhere density
  *does* give the relative one, namely `Y = Set.univ`.

## Implementation notes

The finite-dimensionality hypothesis of the strict forms is not an artefact of the proof. Give
`ℕ ∪ {∗}` the topology whose closed sets are the initial segments `{0, …, n}`, all of `ℕ`, and
the whole space. It is Noetherian, `ℕ` is closed in it, and `ℕ` is nowhere dense because every
nonempty open set contains `∗`; both dimensions are `∞`.

The natural-number form needs the ambient dimension to be nonzero, not merely the ambient space
to be nonempty: a nonempty `X` of dimension `0` with `S = ∅` has `dim S = -∞ < 0 = dim X`, while
both read as `0` after `WithBot.unbotD 0` and `ENat.toNat`. That extra hypothesis is exactly the
one a descending induction has in hand in its inductive step.
-/

@[expose] public section

open Order Set Topology TopologicalSpace

universe u

variable {X : Type u} [TopologicalSpace X]

/-- A nowhere dense closed set contains no irreducible component of a Noetherian space. -/
private theorem IsNowhereDense.false_of_subset_irreducibleComponent [NoetherianSpace X]
    {S : Set X} (hnd : IsNowhereDense S) (hclosed : IsClosed S) {Z : Set X}
    (hZ : Z ∈ irreducibleComponents X) (hZS : Z ⊆ S) : False := by
  obtain ⟨o, hoopen, ⟨x, hx⟩, hoZ⟩ :=
    NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent Z hZ
  rw [IsNowhereDense, hclosed.closure_eq] at hnd
  simpa [hnd] using interior_maximal (hoZ.trans hZS) hoopen hx

/-- **For a closed subset of a Noetherian space, nowhere density is exactly missing every
irreducible component.** This is the criterion a supplier of the nowhere-density hypothesis
checks: in a Noetherian space an irreducible component contains a nonempty open set, so a
component inside `S` gives `S` interior; conversely a nonempty open subset of `S` meets some
component, and a nonempty open subset of an irreducible set is dense in it, so that whole
component lies in `S`. -/
theorem IsClosed.isNowhereDense_iff_forall_irreducibleComponents_not_subset [NoetherianSpace X]
    {S : Set X} (hclosed : IsClosed S) :
    IsNowhereDense S ↔ ∀ Z ∈ irreducibleComponents X, ¬ Z ⊆ S := by
  constructor
  · exact fun hnd Z hZ hZS => hnd.false_of_subset_irreducibleComponent hclosed hZ hZS
  · intro h
    rw [IsNowhereDense, hclosed.closure_eq]
    by_contra hne
    obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hne
    refine h (irreducibleComponent x) (irreducibleComponent_mem_irreducibleComponents x) ?_
    have hmeet : (irreducibleComponent x ∩ interior S).Nonempty :=
      ⟨x, mem_irreducibleComponent, hx⟩
    refine le_trans (subset_closure_inter_of_isPreirreducible_of_isOpen
      (isIrreducible_irreducibleComponent (x := x)).isPreirreducible isOpen_interior hmeet) ?_
    exact hclosed.closure_subset_iff.mpr (Set.inter_subset_right.trans interior_subset)
