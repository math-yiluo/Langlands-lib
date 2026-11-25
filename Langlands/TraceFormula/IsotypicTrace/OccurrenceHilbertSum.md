# An irreducible unitary representation as a Hilbert sum of closures of occurrences

Module `Langlands.TraceFormula.IsotypicTrace.OccurrenceHilbertSum`. Internal to the reduction of
`GroupSchemeCuspidalIsotypicTraceFactorizationStatement` to one local occurrence.

## Setting

`π : A →* (E →L[ℂ] E)` is an action of a group `A` on a complex Hilbert space that preserves
inner products, and `ι : Gv →* A` is a homomorphism. `ρ` is a representation of `Gv`.

## Results

* `adjoint_eq_inv`: the adjoint of `π a` is `π a⁻¹`.
* `orthogonal_invariant`: the orthogonal complement of a subspace invariant under a set of group
  elements closed under inverses is invariant under the same set.
* `starProjection_commute`: if a closed subspace is invariant under `π a` and `π a⁻¹`, its
  orthogonal projection commutes with `π a`. This uses the Library lemma
  `Langlands.Analysis.commute_starProjection_of_invariant`.
* `closureRange_invariant`: the closure of the range of an equivariant linear map
  `j : V → E` (`j (ρ y x) = π (ι y) (j x)`) is invariant under every `π (ι y)`.
* `exists_occurrence_hilbertSum`. Hypotheses: every element of `A` has the form `ι y * c` with
  `c` commuting with the image of `ι`; `E` has no closed `A`-invariant subspaces other than `⊥`
  and `⊤`; and `j₀ : V → E` is a nonzero equivariant linear map. Conclusion: there is a set `𝒜`
  of subspaces of `E` such that each member is the closure of the range of a nonzero equivariant
  linear map `V → E`, the members are pairwise orthogonal, and the closure of their supremum is
  `⊤`.

## Proof of `exists_occurrence_hilbertSum`

Zorn's lemma (`zorn_subset`) gives a maximal set `𝒜` of pairwise orthogonal closures of
occurrences. The proof follows the Library's `compactApproximationOrthogonal`. Let `K` be the
closure of the supremum; it is invariant under `ι(Gv)`. Suppose `K ≠ ⊤`. If `π c (j₀ v) ∈ K` for
every `v` and every `c` commuting with `ι(Gv)`, consider the closed subspace `N` of vectors all
of whose `A`-translates lie in `K`. `N` is `A`-invariant, and by the splitting hypothesis it
contains the range of `j₀`, so `N = ⊤` and then `K = ⊤`, a contradiction. Hence some
`π c (j₀ v)` is not in `K`. Its projection to `Kᗮ` is nonzero, and
`J = P_{Kᗮ} ∘ π c ∘ j₀` is a nonzero equivariant map, because `P_{Kᗮ}` commutes with `ι(Gv)` and
`c` commutes with `ι(Gv)`. The closure of the range of `J` lies in `Kᗮ`. Adding it to `𝒜`
contradicts maximality.

Unlike the tensor-product argument of Getz–Hahn Theorem 3.10.2 and Folland Theorem 7.17, this
step uses no type I property and no tensor products. It uses only one occurrence, which is
supplied as a hypothesis.
