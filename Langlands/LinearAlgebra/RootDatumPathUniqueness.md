# Uniqueness of path enumerations of a Dynkin component

Provenance: internal helper for the even-chain Galois data proof (Task 5375).
That target is derived from Robert Steinberg, *Regular elements of semi-simple
algebraic groups*, Publ. Math. IHÉS 25 (1965), 49–80 (source
`steinberg-1965-regular-elements-semisimple-groups`); the Markdown of the
target `EvenChainGaloisDataStatement` gives the full source account. In the
notation before Theorem 9.11 (printed p.74) Steinberg labels the simple roots
of a component of type `A_n` as `α_1, …, α_n` from one end to the other. This
module proves, as an internal derived result, that such an end-to-end
enumeration is unique up to reversal. It contains elementary combinatorics of
the published predicate `RootDatumPathWeights.IsPathComponent`; no external
source is followed line by line.

Throughout, `P : RootDatum ι M N` is a root datum with a base `b`, and
`β : Fin L → b.support` is an enumeration of simple roots with
`IsPathComponent β`: `L > 0`, the pairings of the enumerated simple roots are
those of a path of type `A_L` (`2` on the diagonal, `-1` between consecutive
entries and `0` otherwise), and every simple root outside the range of `β` is
orthogonal to every entry of `β`.

## Statements

- `IsPathComponent.mem_range_of_pairing_ne_zero`: a simple root `z` with
  `⟨z, β(i)^∨⟩ ≠ 0` for some `i` lies in the range of `β`.
- `IsPathComponent.pairing_succ_ne_zero` and `pairing_pred_ne_zero`:
  consecutive entries of `β` have nonzero pairing, in both orders.
- `IsPathComponent.range_subset`: if `β` and `β'` are path components and some
  entry of `β'` lies in the range of `β`, then the range of `β'` is contained
  in the range of `β`.
- `IsPathComponent.range_eq`: two path components sharing an entry have the
  same range.
- `IsPathComponent.length_eq`: two path components sharing an entry have the
  same length.
- `walk_eq_id_or_rev`: an injective map `π : Fin L → Fin L` such that the
  values of consecutive arguments differ by exactly one is the identity or the
  reversal `j ↦ L - 1 - j` (stated on the underlying natural numbers).
- `IsPathComponent.eq_or_eq_rev`: if two path components `β : Fin L → _` and
  `β' : Fin L' → _` share an entry, then `L' = L` and `β'` equals `β` or its
  reversal `β ∘ Fin.rev`, after the cast along `L' = L`.
- `IsPathComponent.comp_perm`: if a permutation `σ` of the simple roots
  preserves all pairings of simple roots, then `σ ∘ β` is again a path
  component.

## Implemented proof

`mem_range_of_pairing_ne_zero` is the contrapositive of the orthogonality
field of `IsPathComponent`. The two nonvanishing statements rewrite the
pairing of consecutive entries to `-1` using the published lemmas
`pairing_succ_left` and `pairing_succ_right`.

`range_subset` starts at the shared entry `β'(i')` and walks along `β'` in
both directions by induction on the distance. Each next entry of `β'` has
nonzero pairing with the previous one, which already lies on `β`, so it lies
on `β` by `mem_range_of_pairing_ne_zero`. Applying this in both directions
gives `range_eq`. `length_eq` compares cardinalities through the equivalences
`Equiv.ofInjective` given by the injectivity of path enumerations.

`walk_eq_id_or_rev` transfers `π` to a function `ℕ → ℕ`. If `L < 2` the claim
is immediate. Otherwise the first step is either up or down. By induction,
injectivity forbids a change of direction: a step back would revisit the
value two positions earlier. An increasing walk is `j ↦ f(0) + j` and must
start at `0` to stay below `L`. A decreasing walk is `j ↦ f(0) - j` and must
start at `L - 1`.

For `eq_or_eq_rev`, the lengths agree by `length_eq`, so the proof substitutes
`L' = L`. Every entry of `β'` lies on `β` by `range_eq`, which gives an
injective `π` with `β ∘ π = β'`. The pairing table of `β` shows that `π` takes
consecutive arguments to values differing by one. Then `walk_eq_id_or_rev`
gives the two cases.

`comp_perm` transports the pairing table and the orthogonality field along
`σ`: a root outside the range of `σ ∘ β` has its `σ⁻¹`-preimage outside the
range of `β`.
