# Three-sign preservation under integral Galois averaging

Worker 1272.

This internal comparison predicate and its correctness lemmas are derived from
the published integer-valued lattice pairing, integral orbit-sum sign comparison
and actual cocharacter descent. They package the three comparisons used by
`RelativeRootSignsDetermineDynamicStatement`; they do not assume or prove that
statement.

For a commutative group scheme `T` over the spectrum of any commutative integral
domain, a family `Φ` of actual characters, and two actual cocharacters `ν` and
`μ`, `HaveSamePairingSigns T Φ ν μ` means that for every `χ ∈ Φ` the pairings
with `ν` and `μ` have equivalent nonnegative, zero, and strictly positive
conditions. The definition imposes no closure or stability condition on `Φ`.
Reflexivity, symmetry and transitivity follow pointwise from the corresponding
properties of logical equivalence. This comparison predicate contains no
dynamic subgroup equality.

Let `k` and `K` be commutative rings in the same arbitrary universe, with a
`k`-algebra structure on `K`, and suppose `K` is an integral domain. Let `T` be
a commutative group scheme over `Spec k`, let `ν` be an actual cocharacter of
`T_K`, and equip `Aut_k(K)` with a finite enumeration. Let `Φ` be a set of
actual characters of `T_K`. Assume explicitly that:

- `Φ` is stable under the published Galois action;
- the subset of `Φ` pairing nonnegatively with `ν` is stable under that action;
- `χ ∈ Φ` implies `-χ ∈ Φ`.

The theorem `galoisOrbitSum_signs_iff` proves `HaveSamePairingSigns` for the
integral Galois orbit sum of `ν` and `ν` itself: for every `χ ∈ Φ`, pairing
with these two cocharacters has the same nonnegative, zero, and strictly
positive status. Its proof applies the existing
`galoisOrbitSum_nonneg_iff` to `χ` and `-χ`. Bilinearity turns the second
comparison into equivalence of the two nonpositive conditions. The
nonnegative and nonpositive conditions together determine zero and strict
positivity in the integers. In particular, no separate Galois stability
premise for the zero or positive subsets is needed.

Now suppose `k` and `K` are fields, `K/k` is finite dimensional and Galois,
and `T` is affine. Under the same three explicit assumptions on `Φ`,
`descendedOrbitSum_signs_iff` proves `HaveSamePairingSigns` for the base
change of the actual descended orbit sum over `k` and the original `ν`.
The proof rewrites the
published exact recovery equality and applies the preceding result.

The construction uses no division, splitness, smoothness, reductivity, or
restriction on characteristic. The family `Φ` may be empty. Applications
to actual roots must still establish negation closure and the two Galois
stability hypotheses. This module establishes no dynamic subgroup equality
or parabolic classification.
