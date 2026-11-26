# Linear independence of twisted characters

This module proves that the twisted distributions of finitely many pairwise
inequivalent irreducible admissible representations are linearly independent
over `ℂ`. It interpolates prescribed values of those distributions by one
test function in a supplied Hecke corner when all the fixed spaces are nonzero.
The auxiliary results provide small compact open subgroups stable under a
finite-order automorphism and a trace formula on a Hecke corner.

The twisted distribution `Langlands.BaseChange.twistedDistribution μ ρ hρ T` is the
one of the Library module `Langlands.BaseChange.TwistedCharacter.Basic`. It is an
element of `Distribution G` and sends a test function `φ` to the finite-rank trace of
`ρ(φ) ∘ T`, where `ρ(φ)` is `Hecke.integratedAction μ ρ hρ.1 φ`.

## Provenance

The main theorem is a distribution version of HL 2011, II.2.8, Lemma, printed p. 69.
There, for pairwise non-isomorphic σ-stable irreducible smooth `Π_i` of `GL_n(E)` and
isomorphisms `A_i` of `Π_i` onto `Π_i^σ`, Henniart and Lemaire state that the twisted
character functions `Θ^{A_i}_{Π_i}` on the σ-regular set are linearly independent.
They refer to Arthur–Clozel 1989, Ch. 1, Lemma 6.3, for the proof. The Lean
theorem treats distributions on any Hausdorff, locally compact, totally disconnected
group `G` with an automorphism `θ` that preserves small compact open subgroups in the
sense below.

Arthur–Clozel restrict two twisted characters to a common invariant Hecke corner and
use independence of the matrix coefficients of the two fixed-space modules. The
Lean proof extends this argument to a finite family and constructs test functions
with prescribed values. It uses Jacobson density to isolate a fixed-space module
and Burnside's theorem to realize the inverse of its twisting operator on that
space. Bernstein–Zelevinsky 1976, Proposition 2.19, printed p. 21, gives the
finite-family corner argument for ordinary characters, formalized in
`Langlands.Representation.Character.FiniteFamilyProof`.

The interpolation uses the Library's Burnside theorem
`RankOneGraded.exists_forall_eq_smul_of_isSimpleModule`. That theorem uses
Mathlib's scalar-endomorphism form of Schur's lemma
`IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed`.

## Declarations

### `Langlands.BaseChange.exists_compact_openSubgroup_symm_mem`

Let `G` be a Hausdorff, locally compact, totally disconnected topological group and
`θ : G ≃* G` a group automorphism that is continuous and satisfies `θ^N = id` for
some `N > 0` (iterates of the function `θ`). Then every open subgroup `U` contains a
compact open subgroup `K` with `θ⁻¹(k) ∈ K` for every `k ∈ K`.

Proof: the Library lemma `Hecke.TestFunction.commonCompactOpenBiInvariance` (with an
empty family of test functions) gives a compact open subgroup `K₀ ≤ U`. Let `K` be
the set of `g` with `θ^j(g) ∈ K₀` for all `j < N`. It is a subgroup because the `θ^j`
are homomorphisms. It is open as a finite intersection of preimages of `K₀` under the
continuous maps `θ^j`, and compact as a closed subset of `K₀` (the case `j = 0`).
Finally `θ⁻¹ = θ^{N-1}` on `G`, so `θ⁻¹(k)` satisfies the conditions for `j = 0`
(from `j = N-1` for `k`) and for `j ≥ 1` (from `j - 1` for `k`).

Example of use: for a finite Galois extension `E/F` of local fields and `σ` in its
Galois group, `θ = entrywiseAut σ n` on `GL_n(E)` is of this kind. This module does not
prove this; the continuity of `entrywiseAut σ n` and its finite order must be shown
where the lemma is applied.

### `Langlands.BaseChange.mem_fixedVectors_of_twisted`

Let `ρ` be a representation of a group `G` on `V`, `θ : G ≃* G`, and `T` an
endomorphism of `V` with `T ∘ ρ(g) = ρ(θ g) ∘ T` for every `g`. If `K` is a subgroup with
`θ⁻¹(k) ∈ K` for every `k ∈ K`, then `T` maps the `K`-fixed vectors of `ρ` into
themselves.

Proof: for `k ∈ K` and a `K`-fixed `v`, `ρ(k)(T v) = T(ρ(θ⁻¹ k) v) = T v`.

The hypothesis on `T` is the defining relation of the Library's `SigmaIntertwiner`
(lemma `SigmaIntertwiner.comp_apply_eq`, with `θ = entrywiseAut σ n`), that is, of an
isomorphism of `Π` onto `Π^σ` as in HL II.1.3 and II.2.7.

### `Langlands.BaseChange.twistedDistribution_corner_of_preserves_fixedVectors`

Let `μ` be a Haar measure on `G`, `ρ` an admissible representation on `V`, `T` an
endomorphism of `V`, and `K` a compact open subgroup such that `T` maps the `K`-fixed
vectors into themselves. For every element `e` of the Hecke corner
`Hecke.HeckeAlgebra.Corner μ K hK`, the twisted distribution evaluated at the test
function of `e` equals the ordinary trace, on the finite-dimensional space of
`K`-fixed vectors, of the corner action of `e` composed with the restriction of `T`.

Proof: the operator `ρ(e) ∘ T` has range inside the `K`-fixed vectors
(Library lemma `Hecke.integratedAction_range_le_fixedVectors`), so its finite-rank
trace is the trace of its restriction to that subspace (Library lemma
`FiniteRankEnd.trace_eq_subspace`).

### `Langlands.BaseChange.exists_twistedDistribution_corner_values`

Let `G` be a Hausdorff, locally compact, totally disconnected topological group with
its Borel sigma-algebra and a Haar measure `μ`. Let `θ : G ≃* G` and let `K` be a
compact open subgroup with `θ⁻¹(k) ∈ K` for every `k ∈ K`. Let `ι` be a finite type.
For each `i : ι` let `ρ i` be an irreducible admissible representation of `G` on a
complex vector space `V i` with a nonzero `K`-fixed vector, and let `T i` be an
injective endomorphism of `V i` with `T i ∘ ρ i g = ρ i (θ g) ∘ T i` for every `g`.
Assume that the `ρ i` are pairwise inequivalent. For any family of complex numbers
`c i`, there is one element of the Hecke corner `H_K` whose test function has
twisted trace `c i` in `(ρ i, T i)` for every `i`.

All the spaces `V i` lie in one universe. The `T i` need only be injective, not
surjective.

Proof. Let `M i` be the space of `K`-fixed vectors of `ρ i`. Then:

1. `M i` is nonzero (it contains `v i`), finite-dimensional (admissibility), and a
   simple module over the Hecke corner `H_K` (Library lemma
   `CompactCoefficientClass.isSimpleModule_fixedVectors`).
2. The `M i` are pairwise non-isomorphic `H_K`-modules: an `H_K`-isomorphism
   `M i ≅ M j` would give an equivalence `ρ i ≅ ρ j` by the Library lemma
   `Hecke.nonempty_equiv_of_cornerAction_eq_zero_iff`.
3. `T i` restricts to an injective, hence bijective, endomorphism `B i` of `M i`
   (`mem_fixedVectors_of_twisted`).

For each `j` the Library lemma `FiniteSimpleTrace.exists_action_projection` gives
`r : H_K` acting as the identity on `M j` and as zero on `M i` for `i ≠ j`.
Burnside's theorem gives `s : H_K` acting on `M j` as the inverse of `B j`.
By the corner trace formula, the twisted trace of `r * s` vanishes for
`i ≠ j` and equals the dimension of `M j` for `i = j`, since the composition
with `B j` is the identity there. Divide by this nonzero dimension to obtain
an element `e j` with traces `1` at `j` and `0` elsewhere. The linear
combination `∑ j, c j • e j` has the prescribed values.

### `Langlands.BaseChange.exists_twistedDistribution_test_values`

Suppose instead that every open subgroup contains a compact open subgroup
`K` with `θ⁻¹(K) ⊆ K`. With the same hypotheses on the family except for the
fixed-vector condition, any family of values is realized by a test function.
For each `i` choose a nonzero vector and an open subgroup fixing it. Choose
`K` as in the hypothesis inside the finite intersection of those subgroups.
Apply fixed-corner interpolation, and take the test function of the corner
element it supplies.

### `Langlands.BaseChange.twistedDistribution_linearIndependent`

Under the hypotheses of `exists_twistedDistribution_test_values`,
`i ↦ twistedDistribution μ (ρ i) (hρ i) (T i)` is linearly independent over `ℂ`.
For each index `j`, interpolate the vector with value `1` at `j` and `0`
elsewhere and evaluate any linear relation at the resulting test function.
The value is exactly the coefficient at `j`, so that coefficient is zero.

### `Langlands.BaseChange.twistedDistribution_linearIndependent_of_iterate`

The same conclusion when `θ` is a continuous automorphism with `θ^N = id` for some
`N > 0`. It combines the two previous results through
`exists_compact_openSubgroup_symm_mem`.

## Sources

- G. Henniart and B. Lemaire, *Changement de base et induction automorphe pour GL_n en
  caractéristique non nulle*, Mém. Soc. Math. France 124 (2011), II.1.3 and II.2.7
  (twisted characters), II.2.8, Lemma, printed p. 69 (linear independence of twisted
  character functions).
- J. Arthur and L. Clozel, *Simple Algebras, Base Change, and the Advanced Theory of
  the Trace Formula*, Annals of Mathematics Studies 120 (1989), Ch. 1, Lemma 6.3,
  printed p. 52 (twisted character independence for two representations).
- I. N. Bernstein and A. V. Zelevinsky, *Representations of the group GL(n,F) where F is
  a non-archimedean local field*, Russian Math. Surveys 31:3 (1976), Proposition 2.19,
  printed p. 21 (the untwisted argument through Hecke corners).
