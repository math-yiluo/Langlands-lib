# Normalized linear comparison of level Hecke spaces

Module `Langlands.Representation.Hecke.LevelHeckeCornerLinear`. All declarations are
in `Langlands.Hecke.LevelCorner`; the group has universe `u`.

This is an internal construction for the published
`Langlands.Hecke.LevelHeckeCornerComparisonStatement`. Its main definition is
`linearEquiv μ K hK`, a complex linear equivalence

```text
LevelHeckeAlgebra ℂ K.toSubgroup ≃ₗ[ℂ] HeckeAlgebra.Corner μ K hK.
```

The construction assumes a topological group `G`, a Borel measurable structure,
a left Haar measure `μ`, and a compact open subgroup `K` with compactness proof
`hK`. It does not require the additional Hausdorff, nonarchimedean, or local
compactness assumptions of the eventual comparison statement.

Write `m = (μ.real (K : Set G) : ℂ)`. The equivalence satisfies
`linearEquiv μ K hK a x = m⁻¹ * a.1 (x : G ⧸ K.toSubgroup)`.
This module establishes the linear equivalence and this pointwise formula.
Multiplicativity and compatibility with representation actions are separate
proof obligations.

## Construction and implemented proofs

`evaluation μ x` is the linear evaluation map on the actual Hecke test functions.
`cosetTest μ K hK q` is the left translate by `q.out` of the normalized subgroup
indicator. `cosetTest_apply` identifies it with `m⁻¹` on the coset `q` and zero
elsewhere. The proof uses the quotient equality criterion
`q.out⁻¹ * x ∈ K` and `QuotientGroup.out_eq'`.

`expansion` is `Finsupp.linearCombination` of these coset tests.
`expansion_apply` evaluates the finite sum; precisely the term indexed by `xK`
can contribute. If that coset is outside the coefficient support, the
coefficient is zero. This gives the displayed pointwise formula for arbitrary
finitely supported coefficient functions.

`level_invariant` extracts left invariance from the fixed-vector property of
the permutation representation, by evaluating that property at `k • q`.
For a level Hecke element, `expansion_mem` uses this left invariance and the
identity `(xk)K = xK` to put its expansion in the bi-invariant subalgebra.
`toCorner` is the resulting linear map to the corner.

`toCorner_injective` evaluates an equality at representatives of all quotient
cosets and cancels `m⁻¹`. Nonvanishing of `m` comes from the published
`HeckeAlgebra.compactOpen_complex_mass_ne_zero`.

For surjectivity, `finite_coset_support` covers the compact support of an actual
test function by open sets `iK`. A finite subcover yields finitely many quotient
cosets containing every representative at which the test is nonzero.
`out_value` uses right invariance of a corner function `f` to show
`f (Quotient.out (xK)) = f x`.

`coefficients f` is the finitely supported function `q ↦ m * f q.out`;
`coefficients_mk` evaluates it at `xK`. `coefficients_fixed` uses left invariance
of `f` and the formula for the permutation representation to show that these
coefficients are fixed by `K`. Their expansion equals `f`, because `m⁻¹ * m = 1`.
This proves `toCorner_surjective`. Finally, `linearEquiv` is
`LinearEquiv.ofBijective toCorner`, and `linearEquiv_apply` inherits the
pointwise formula.

## Provenance and scope

These definitions and auxiliary lemmas implement the standard normalized coset
comparison explained in the paired Markdown of
[LevelHeckeCornerComparisonStatement](LevelHeckeCornerComparisonStatement.md).
They are derived from the published coset permutation representation,
normalized indicator, and bi-invariant corner constructions, rather than a
separate assertion from the literature. The finite-subcover argument is the
`xK` counterpart of the published `Kx` argument in
`finite_leftCoset_expansion` in the module `CompactTensorFiniteCosets`.
No target declaration or imported Library file is changed.

The only import is the published
`Langlands.Representation.Hecke.LevelHeckeCornerComparisonStatement`, which
provides the level and Haar Hecke spaces.
