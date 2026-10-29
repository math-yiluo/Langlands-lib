# Finite orientation closure and its unique lattice extrema: proof

Author: Worker 903.

This module proves the published proposition
`Langlands.Combinatorics.OrientationClosureExtremaStatement.{uE}` from
`Langlands.Combinatorics.OrientationClosureStatement` as the theorem
`Langlands.Combinatorics.orientationClosureExtrema`. It imports only that
statement module and `Mathlib.Data.Fintype.Basic`; there are no project
representation or classification imports, no additional hypotheses, no
`sorry` and no new axioms. The kernel reports only `propext`,
`Classical.choice` and `Quot.sound`.

The statement fixes an arbitrary `E : Type uE` with `[Fintype E]` and
`[DecidableEq E]` and an arbitrary `o₀ : E → Bool`. Its local bindings are
`opposite := fun e => !(o₀ e)`, the halfspaces `H e := {o | o e = o₀ e}`, and
`Closed S`, meaning that `Function.update o e (o₀ e) ∈ S` whenever `o ∈ S` and
`o e ≠ o₀ e`. The theorem introduces these `let` bindings and proves the four
clauses directly. No step uses a nonempty or positive-cardinality edge type.

## Finite correction

The private definition `correctOn o₀ T o` is the orientation that equals
`o₀ e` on the edges `e ∈ T` of a finset `T : Finset E` and equals `o e` off
`T`. The private lemma `correctOn_mem` says: if `S` satisfies the closure
condition and `o ∈ S`, then `correctOn o₀ T o ∈ S` for every finset `T`.

The proof is `Finset.induction_on` on `T`.

- For `T = ∅`, `correctOn o₀ ∅ o = o` by function extensionality, so the
  claim is `o ∈ S`.
- For `insert a T` with `a ∉ T`, the value of `correctOn o₀ T o` at `a` is
  `o a`. If `o a = o₀ a`, then `correctOn o₀ (insert a T) o` equals
  `correctOn o₀ T o`, and the induction hypothesis applies. Otherwise
  `correctOn o₀ (insert a T) o` equals
  `Function.update (correctOn o₀ T o) a (o₀ a)`. The corrected orientation
  still disagrees with `o₀` at `a`, so one application of the closure
  condition to the induction hypothesis gives membership.

Each such equality is proved pointwise by splitting on `e = a`.

Two private Boolean facts, both checked by `decide` over the two values of
each argument, are `bool_ne_not_iff : a ≠ !b ↔ a = b` and
`bool_not_of_ne : a ≠ b → (!b) = a`.

## Clause 1: the two extrema

*Nonempty iff contains the reference.* If `o ∈ S`, then `correctOn_mem` with
`T = Finset.univ` puts `correctOn o₀ Finset.univ o` in `S`. That orientation
is `o₀` pointwise, so `o₀ ∈ S`. Conversely, `o₀ ∈ S` witnesses
`S.Nonempty`. Finiteness of `E` enters exactly here, through `Finset.univ`.

*Proper iff omits the opposite orientation.* Suppose `S ≠ Set.univ` and
`opposite ∈ S`. Take any target `t : E → Bool` and correct `opposite` on the
finset `Finset.univ.filter fun e => t e = o₀ e`. On an edge with
`t e = o₀ e`, the corrected value is `o₀ e = t e`. On any other edge it stays
`opposite e = !(o₀ e)`, and `bool_not_of_ne` turns `t e ≠ o₀ e` into
`!(o₀ e) = t e`, using the fact that `Bool` has only two values. So the
corrected orientation is `t`, which lies in `S` by `correctOn_mem`. Since `t`
was arbitrary, `Set.eq_univ_of_forall` gives `S = Set.univ`, a contradiction.
For the reverse direction, if `opposite ∉ S` then `S = Set.univ` is
impossible, because `opposite ∈ Set.univ`.

## Clause 2: the basic closed sets

- `∅`: there is no member, by `Set.notMem_empty`.
- `Set.univ`: every update lies in `Set.univ`.
- `{o₀}`: a member is `o₀` itself, which disagrees with `o₀` on no edge, so the
  hypothesis `o₀ e ≠ o₀ e` is refuted by `rfl`.
- `{opposite}ᶜ`: if `Function.update o e (o₀ e) = opposite`, then evaluating at
  `e` gives `o₀ e = !(o₀ e)`, which `simp` refutes. So the update stays in the
  complement. This holds for every member, whatever its other values.
- `H a`: the goal is `Function.update o e (o₀ e) a = o₀ a`. If `a = e`, the
  update evaluates to `o₀ a`. If `a ≠ e`, `Function.update_of_ne` reduces the
  goal to `o a = o₀ a`, which is the membership hypothesis `o ∈ H a`.

## Clause 3: intersections and unions

Let `𝒮` be any set of closed sets; it may be empty. For `⋂₀ 𝒮`, after
`Set.mem_sInter`, the member `o` lies in every `S ∈ 𝒮`, and closedness of each
such `S` puts the update in each of them. When `𝒮 = ∅` this is
`Set.univ`, and the argument is vacuous in `S`. For `⋃₀ 𝒮`, a member `o` lies
in some `S ∈ 𝒮`, and closedness of that `S` puts the update in the same `S`.
When `𝒮 = ∅` there is no member.

## Clause 4: halfspace identities

Both identities are proved by `Set.ext`.

- `(⋂ e, H e) = {o₀}`: membership on the left is `∀ e, o e = o₀ e`
  (`Set.mem_iInter`). This is `o = o₀` by `funext`, and conversely by
  rewriting.
- `(⋃ e, H e) = Set.univ \ {opposite}`: membership on the left is
  `∃ e, o e = o₀ e` (`Set.mem_iUnion`). Membership on the right simplifies, via
  `Set.mem_sdiff`, `Set.mem_univ` and `Set.mem_singleton_iff`, to
  `o ≠ opposite`. If `o e = o₀ e` and `o = opposite`, evaluating at `e` gives
  `o e = !(o₀ e)`, contradicting `bool_ne_not_iff`. Conversely, if no edge has
  `o e = o₀ e`, then `bool_ne_not_iff` gives `o e = !(o₀ e)` at every edge, so
  `o = opposite` by `funext`.

## Empty edge type

The proof uses no case split on `E`. When `E` is empty, every function
`E → Bool` equals `o₀` and `opposite` by extensionality. `Finset.univ` is
empty and `correctOn o₀ Finset.univ o = o₀` holds trivially. The intersection
over no halfspaces is `Set.univ = {o₀}` and their union is
`∅ = Set.univ \ {opposite}`. All four clauses therefore follow from the same
argument with no extra assumption.

## Relation to the source

The statement was derived from Zelevinsky (1980), §2.8, condition (★),
Theorem proof step (1), and the proof of Proposition 2.10, printed
pp.179–180 (PDF16–17). The literature ID is `zelevinsky-1980-induced-ii`,
with SHA-256
`663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`. I reread
those pages; there is no project erratum for this source. Two printed claims
correspond to the Lean clauses:

- Step (1) says that if `Γ⃗ᵗ ∈ 𝒪` then (★) forces `𝒪 = 𝒪(Γ)`. This is the
  second half of clause 1, proved here by explicit finite correction.
- The proof of Proposition 2.10 uses `⋂_γ 𝒪(λ, γ) = {Γ⃗(λ)}` and
  `⋃_γ 𝒪(λ, γ) = 𝒪(Γ) \ {Γ⃗ᵗ}`. This is clause 4.

The source also notes that each halfspace satisfies (★), as part of clause 2.
The source does not print the rest separately: nonempty iff contains the
reference, closedness of `∅`, `Set.univ`, `{o₀}` and `{opposite}ᶜ`, and
closure under arbitrary intersections and unions. These are elementary facts
made explicit in the statement and proved here.

This proof does not establish the combinatorial lattice equality of the
§2.8 Theorem, step (1), that the (★)-closed sets are exactly the lattice
generated by the halfspaces.
It also proves nothing about submodules, about realizing halfspaces by the
submodules `π(λ, γ)`, or about the irreducible submodule and quotient of
Proposition 2.10.
