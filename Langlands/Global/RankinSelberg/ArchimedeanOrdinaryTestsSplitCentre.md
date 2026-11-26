# Ordinary archimedean tests on the split centre and the untwisting premise

Module `Langlands.Global.RankinSelberg.ArchimedeanOrdinaryTestsSplitCentre`, namespace
`Langlands.Global.RankinSelbergGlobal`. The published surjectivity statements
`CuspidalPairPoles.RealPlaceWhittakerRestrictionSurjectivityStatement` and
`CuspidalPairPoles.ComplexPlaceWhittakerRestrictionSurjectivityStatement` (module
`CuspidalPairPoleLocalRanges`) apply only to cuspidal realizations trivial on the split centre:
`CuspidalPairPoles.IsTrivialOnSplitCentre T` says that every function of `T` is invariant under
the scalar matrices `a I` with `a` a positive real scalar idele (the same positive real at every
infinite place and `1` at the finite places). This module restricts the four ordinary
nonvanishing statements to such realizations, proves the restricted statements from local
generation and the published surjectivity, and isolates the passage to arbitrary realizations as
one premise.

## Statements

The four restricted statements have the binders and conclusions of the corresponding statements
of the modules [`UnequalPlaceTestsFromOrdinary`](UnequalPlaceTestsFromOrdinary.md) and
[`ArchimedeanFactorizationOrdinaryReduction`](ArchimedeanFactorizationOrdinaryReduction.md), with
the two hypotheses `IsTrivialOnSplitCentre T` and `IsTrivialOnSplitCentre T'` added after the
two realizations:

| Restricted statement | Unrestricted statement |
| --- | --- |
| `RealUnequalOrdinaryPlaceTestsSplitCentreStatement` | `RealUnequalOrdinaryPlaceTestsStatement` |
| `ComplexUnequalOrdinaryPlaceTestsSplitCentreStatement` | `ComplexUnequalOrdinaryPlaceTestsStatement` |
| `RealEqualOrdinaryPlaceTestsSplitCentreStatement` | `RealEqualOrdinaryPlaceTestsPositiveRankStatement` |
| `ComplexEqualOrdinaryPlaceTestsSplitCentreStatement` | `ComplexEqualOrdinaryPlaceTestsPositiveRankStatement` |

Each asserts, for the given realizations, place, scale `a` of `ψ` and parameter lists, a pair of
actual restrictions (for `ψ` and `ψ⁻¹`), quotient measure data and, in equal rank (`0 < r`), a
Schwartz function on the last-row space, such that the ordinary integral is nonzero at points
arbitrarily far to the right.

`OrdinaryPlaceTestsUntwistStatement` is the conjunction of the four implications from each
restricted statement to the corresponding unrestricted one.

## Why the untwisting premise holds

This module does not prove `OrdinaryPlaceTestsUntwistStatement`; the following argument shows
why it holds. Every actual cuspidal realization `T` becomes trivial on the split centre after a
twist by `‖·‖^(-λ) ∘ det` for some complex `λ`. This is the published
`NormPowerTwist.exists_normPower_twist_isTrivialOnSplitCentre` (module
`CuspidalNormPowerTwist`), applied with the twist `T.heckeDeterminantTwist`. Twist both
realizations of a pair in this way and apply the restricted statement. Three further facts would
carry its conclusion back to the original pair:

- the twisted realization has, at each archimedean place, the parameter list of `T` with every
  exponent shifted by `-λ`, so the restricted statement applies to it. At complex places the
  Library proves this transport for arbitrary Hecke characters (module
  `ComplexPlaceParameterHeckeTwist`); at real places the analogous transport for norm powers is
  needed;
- the global Whittaker function of a twisted vector is the original one times
  `‖det‖^(-λ)`, since the determinant is trivial on the unipotent radical. So an actual
  restriction of the twist at a place is `|det|^(-λ)` (normalized absolute value) times an
  actual restriction of `T`, up to a nonzero constant from the finite point;
- multiplying the two restrictions by `|det|^λ` and `|det|^λ'` shifts the spectral variable of
  the ordinary integral by `λ + λ'`, in both rank cases, because
  `|det diag(g, 1)| = |det g|`. Nonvanishing at points arbitrarily far to the right is
  invariant under such a shift.

## Results

- `realOrdinaryPlaceTestsSplitCentre_of_generation`: from
  `RealOrdinaryNormalizedGenerationStatement` and the published real surjectivity statement,
  the two restricted real statements. Each is an instance of `exists_realUnequalOrdinaryTest`,
  resp. `exists_realEqualOrdinaryTest` (module `ArchimedeanOrdinaryTestsFromGeneration`). Their
  surjectivity hypotheses are supplied by the published statement, whose split-centre
  hypothesis is now available.
- `complexOrdinaryPlaceTestsSplitCentre_of_generation`: the same at complex places, with
  `ComplexOrdinaryNormalizedGenerationStatement`, the published complex surjectivity statement
  and `exists_complexUnequalOrdinaryTest`, `exists_complexEqualOrdinaryTest`.
- `archimedeanFactorizationSplitCentreReduction` proves

```
def ArchimedeanFactorizationSplitCentreReductionStatement : Prop :=
  InfiniteWhittakerSliceModelStatement.{u, uQ} → RealPlaceFunctionalEquationStatement.{u} →
    RealOrdinaryNormalizedGenerationStatement → ComplexOrdinaryNormalizedGenerationStatement →
    CuspidalPairPoles.RealPlaceWhittakerRestrictionSurjectivityStatement.{u} →
    CuspidalPairPoles.ComplexPlaceWhittakerRestrictionSurjectivityStatement.{u} →
    OrdinaryPlaceTestsUntwistStatement.{u} → ArchimedeanFactorizationStatement.{u, uQ}
```

  by untwisting the four restricted statements with the premise and applying
  `archimedeanFactorizationOrdinaryReduction`.

The proofs use only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

## Provenance

Internal. The restricted statements and the untwisting premise are Library interfaces chosen
to match the split-centre hypothesis of the published surjectivity statements. Twisting by a
norm power is a classical normalization: H. Jacquet and J. A. Shalika, *On Euler products and
the classification of automorphic forms II*, Theorem 4.2, printed pp. 806–807, displays (1)
and (4), twist by a norm power with real exponent to make the representation unitary. Such a
twist leaves the phase of the central character on the positive scalar ideles in place; for
instance the unitary idele class character `‖·‖^i` of `GL_1` is nontrivial there. Triviality
on the split centre requires a complex exponent, which the published
`NormPowerTwist.exists_normPower_twist_isTrivialOnSplitCentre` (module `CuspidalNormPowerTwist`)
supplies. The route sketched above for the untwisting premise uses that theorem together with
the three transport requirements listed there. The archimedean local tests are those used in
J. W. Cogdell, *Analytic theory of L-functions for GL_n* (2004), proof of Theorem 4.1, printed
pp. 219–220; the generation premises formulate consequences of H. Jacquet, *Archimedean
Rankin–Selberg integrals* (2009), Theorems 2.3, 2.6 and 2.7, as described in the Markdown of
`ArchimedeanOrdinaryTestsFromGeneration`.
