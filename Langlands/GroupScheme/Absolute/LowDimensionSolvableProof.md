# Proof: connected group varieties of dimension at most two are solvable

The theorem `Langlands.GroupScheme.lowDimensionSolvable.{u}` proves the unchanged
published proposition `Langlands.GroupScheme.LowDimensionSolvableStatement.{u}`.
For every algebraically closed field `k` and every smooth connected affine group
scheme `G` over `Spec k`, a bound of two on `Lie.dimension G` implies
`IsSolvableGroupScheme G`. There are no additional hypotheses.

## Source and provenance

The target is Corollary 17.27, printed p.360 of James S. Milne, *Algebraic Groups:
The theory of group schemes of finite type over a field* (2017), registered source
`milne-2017-algebraic-groups`. The Section 17b convention (p.353) supplies a
connected group variety over an algebraically closed field; the chapter's affine
convention is on p.352. Proposition 1.37 (p.18) identifies its dimension with its
Lie dimension because it is smooth. The target's Markdown records this source
correspondence and the geometric-points meaning of the solvability predicate.

The registered official errata snapshot of 2026-11-02,
`milne-2017-algebraic-groups-errata-2026-11-02`, corrects the example following the
corollary on p.360 to use `SL₂`; it does not change the corollary. Milne's printed
proof uses a Borel subgroup and nilpotence in dimensions at most one. This module
instead gives a derived proof from the Library's published unipotent-radical,
reductivity, maximal-torus, and adjoint-weight results. Its private lemmas are
internal consequences of those results and ordinary finite-dimensional linear
algebra.

## Implemented proof

1. A split torus with a nonzero character has a nonempty set of split factors:
   its character lattice is the integer-valued functions on that set. The
   published infinitesimal coordinates identify its Lie dimension with the
   number of factors, so this dimension is positive.
2. If a split maximal torus of a connected reductive group has a root `α`,
   root negation supplies the root `-α`. They are distinct because an
   integer-valued character equal to its negative is zero. Their nonzero weight
   spaces and the zero-weight space are independent. The latter contains the
   injective differential of the torus and is positive-dimensional by step 1.
   The finite-dimensional submodule dimension formula therefore gives at least
   three dimensions in the ambient Lie algebra.
3. Over an algebraically closed field a maximal torus is split. For a connected
   reductive group of dimension at most two, step 2 excludes all roots. The
   published rootless reductive-group theorem makes the maximal torus inclusion
   an isomorphism. A commutative group scheme is solvable, and solvability
   transports across this isomorphism.
4. For the original group, take its represented ground-field unipotent radical
   `U` and represented fppf quotient `Q`. The quotient is pseudo-reductive, hence
   connected reductive over the perfect algebraically closed ground field.
   The smooth kernel makes the quotient projection smooth, so its differential
   is surjective and `Lie.dimension Q ≤ Lie.dimension G`. Step 3 makes `Q`
   solvable, and the published extension theorem through an affine unipotent
   fppf kernel makes `G` solvable.

The proof imports the target without editing it or its import closure. It
applies in every universe and every characteristic; distinctness of opposite
characters is proved in the integral character lattice.
