# Cuspidal discreteness from compactness of cuspidal convolutions

`Langlands.Automorphic.GroupSchemeFunctions.GroupSchemeFullAEL2CuspidalDecompositionStatement`
is a proposition definition. It supplies no proof.

## Setting

The objects are the Library's actual full almost-everywhere cuspidal space
and its right action. The hypotheses are those of
`GroupSchemeFullAEL2Integrated`:

- `F` is a number field and `G` a connected reductive affine group scheme
  over `Spec F`, locally of finite type.
- The parabolic–cocharacter theorem `ParabolicDynamicStatement` is an
  explicit argument.
- `T` is a split central torus with injective, finite-index character
  restriction.
- The Haar measure on the norm-one subgroup is right invariant.

`S` is `fullAEL2CuspidalSubmodule`, the closed subspace of
`L²(PositiveRationalQuotient)` of classes whose actual mass-one constant
terms along every proper rational parabolic vanish almost everywhere. Its
completeness is the published instance from
`groupSchemeParabolicL2Closedness`. `πc` is
`fullAEL2CuspidalBoundedRightAction`, the original right action restricted
to `S`.

## Hypothesis and conclusion

The hypothesis is that for every compactly supported continuous
`f : C_c(G(A_F), ℂ)`, the existing operator
`fullAEL2CuspidalIntegratedAction F G hPD hG T i hi I e hc Measure.haar f hf`
is compact. That operator is `R(f)` on `S` for the ambient left Haar
measure.

The conclusion is that there is a set `A` of closed subspaces of `S` with
three properties.

1. Every member is nonzero, closed, `πc`-invariant and topologically
   irreducible.
2. The inclusions of the members form a Mathlib `IsHilbertSum` of `S`.
3. Each member is `πc`-intertwining isometric to only finitely many
   members.

No compactness, trace-class property or rapid decay is proved here. The
hypothesis is the remaining analytic input, Getz–Hahn Theorem 9.1.2.

## Sources and provenance

This is a derived statement. The source is Getz–Hahn, *An Introduction to
Automorphic Representations* (2024), registered as
`getz-hahn-2024-automorphic-representations`, SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.

- Theorem 9.1.2, printed p.241 (one-based PDF p.253), proves that the
  cuspidal restriction of `R(f)` is trace class, hence compact.
- Corollary 9.1.3 on the same page derives the discrete decomposition of the
  cuspidal subspace with finite multiplicities, via Lemma 9.3.1 and
  Corollary 9.3.2, printed p.247.

The statement records the step "Theorem 9.1.2 implies Corollary 9.1.3" on
the actual Library objects, with the weaker compactness hypothesis in place
of trace class.

The almost-everywhere cuspidality condition is exactly the one implemented
in `GroupSchemeFullAEL2`, with norm-one Haar measure as the translation
measure. Its relation to GH (6.20)–(6.21) is documented in that module and
is inherited unchanged.

## Intended proof

A private proof compiles. It applies the separately staged
`InvariantSubspaceDiscreteDecompositionStatement`, with `E = S` and
`V = ⊤`, to `πc`:

- `πc` preserves norms, by `norm_fullAEL2CuspidalBoundedRightAction`, and
  hence inner products.
- Its orbits are continuous, by `fullAEL2CuspidalOrbitMap`.
- Composing the hypothesis with the inclusion of `⊤` preserves
  compactness.

Mathlib's `IsHilbertSum.mkInternal` then packages the orthogonal dense
family.
