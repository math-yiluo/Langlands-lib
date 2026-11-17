# Closed root sets without opposite roots lie in a positive system

This module contains root-system combinatorics over `ℤ` that the clause-3 part of
[`AffineSplitRootSubgroupSpanning`](../GroupScheme/Reductive/AffineSplitRootSubgroupSpanning.md)
needs. Everything is in namespace `Langlands.LinearAlgebra`. The module adds theorems only:
no definitions, statements or axioms.

## Source

The main theorem `exists_base_isPos_of_closed` is the implication "(3) ⇒ (1)" of Conrad,
*Reductive group schemes* (2014), Lemma 5.1.15, pp.146–147 (Library source
`conrad-2014-reductive-group-schemes`). It says that a closed set `Ψ` of roots with
`Ψ ∩ -Ψ = ∅` is contained in a positive system of roots. Conrad cites this implication as
Bourbaki, *Lie groups and Lie algebras*, Ch. VI, §1.7, Prop. 22. The proof below is not
Bourbaki's Weyl-chamber argument. It is an integral Gordan alternative, described next.

## Results

- `exists_mul_add_pos p q hp`: for integer families `p`, `q` indexed by `Fin k`, with every
  `p j > 0`, some integer `N` makes every `N * p j + q j` positive. The proof takes
  `N = ∑ |q j| + 1`.
- `gordan_int k v` (**Gordan's alternative over `ℤ`**): for vectors `v : Fin k → (I → ℤ)`,
  `I` finite, either some `ℤ`-linear functional `f` has `0 < f (v j)` for all `j`, or some
  nonzero family `c : Fin k → ℕ` has `∑ c j • v j = 0`. The proof is by induction on `k`.
  If the old vectors admit such an `f` and the new vector `x` has `f x < 0`, the old
  vectors are projected along `x` and the induction hypothesis is applied again. A
  positive functional on the projected vectors combines with `f` into a functional that is
  positive on all the vectors. A natural relation among the projected vectors expands to
  one among all the vectors. If `f x = 0` and `x ≠ 0`, a large multiple of `f` plus the
  coordinate functional `x i • proj i` works. If `f x = 0` and `x = 0`, the relation is
  the indicator of the new index. If `f x > 0`, `f` itself works. A natural relation among
  the old vectors extends by zero.
- `multiset_sum_mem_of_closed` (integral saturation): let `S` be a set of roots that is
  closed under sums that are roots. Every multiset of members of `S` whose sum is a root
  has its sum in `S`. The proof is strong induction on the multiset. If `s.sum = α_i`, then
  `∑ ⟨α, α_i^∨⟩ = 2`, so some member `α = α_j` has positive pairing with `α_i^∨`. If
  `j = i` the sum is already `α ∈ S`. Otherwise `s.sum - α = α_i - α_j` is a root,
  by Mathlib's `RootPairing.root_sub_root_mem_of_pairingIn_pos`. The induction hypothesis
  puts `s.sum - α` in `S`, and closedness puts `s.sum` in `S`.
- `multiset_sum_ne_zero_of_closed`: for `Ψ` closed with `Ψ ∩ -Ψ = ∅`, no nonempty multiset
  of roots of `Ψ` sums to zero. If it did, removing one member `α_a` would leave a multiset
  summing to the root `-α_a`. Saturation would then put `-α_a = α_c` with `c ∈ Ψ`, which
  contradicts `α_a + α_c ≠ 0`.
- `mem_of_root_eq_nsmul_add_nsmul`: if `a, c ∈ Ψ`, `Ψ` is closed, and the root `α_d`
  equals `p α_a + q α_c` with `p, q : ℕ`, then `d ∈ Ψ`. This is saturation applied to the
  multiset with `p` copies of `α_a` and `q` copies of `α_c`.
- `exists_base_isPos_of_closed P Ψ hcl hopp`: for a reduced root datum
  `P : RootDatum J (I → ℤ) (I → ℤ)` with `J` finite, a closed `Ψ` with `Ψ ∩ -Ψ = ∅` has a base
  `b : P.Base` such that every member of `Ψ` is `b`-positive. Gordan's alternative is
  applied to the roots of `Ψ`, enumerated by `Fin (Nat.card Ψ)`.
  - A natural relation is impossible by `multiset_sum_ne_zero_of_closed`.
  - A functional `f` positive on `Ψ` gives the functional `f ∘ P.flip.Polarization` on
    the coweight lattice. It is positive on the corresponding coroots by the Library's
    `SplitExistence.dual_polarization_root_pos_iff`. The Library's
    `exists_base_isPos_of_pos` then produces a base for which these roots are positive.

The closedness hypotheses use the encoding of
[`AffineSplitRootSubgroupSpanningStatement`](../GroupScheme/Reductive/AffineSplitRootSubgroupSpanningStatement.md):
`∀ a ∈ Ψ, ∀ c ∈ Ψ, ∀ d, P.root d = P.root a + P.root c → d ∈ Ψ` and
`∀ a ∈ Ψ, ∀ c ∈ Ψ, P.root a + P.root c ≠ 0`.

## Provenance

These are internal lemmas. Their mathematical content is standard root-system theory,
covered by Conrad's Lemma 5.1.15 and Bourbaki's Prop. 22, but the integral Gordan route is
specific to this module.
