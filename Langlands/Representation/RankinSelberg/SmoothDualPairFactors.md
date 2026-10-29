# Actual smooth-dual pair factors

Author: Worker 31.

This internal construction applies the published Gelfand–Kazhdan realization
to the Whittaker and Rankin–Selberg transport APIs. Its selected L-factor is
the factor of the actual smooth-dual pair, constructed from an explicit
`DualPairLPolynomialExists` proof. It also transports the existing p-adic
L-polynomial, epsilon and gamma relations to actual smooth contragredients.

## Provenance and conventions

The module imports the following published mathematics by Lean module name:

- `Langlands.Representation.Smooth.Contragredient.GelfandKazhdanProof`
  supplies `Langlands.gelfandKazhdanContragredient`.
- `Langlands.Representation.RankinSelberg.DualWhittakerType` supplies
  long-Weyl equivalences of the complete functional spaces and preservation
  of the complete Whittaker-type predicate by inverse transpose.
- `Langlands.Representation.RankinSelberg.WhittakerTypeEquivalence` supplies
  functional-space and full-type transport through representation
  equivalences.
- `Langlands.Representation.RankinSelberg.PadicPairFactors` supplies the
  p-adic symmetric relations and their equivalence invariance. Its import
  closure supplies `PairLFactor` and the normalized-polynomial constructor.

The present contribution introduces an application of these APIs rather than
a new theorem attributed to an original source. The imported modules and their
paired Markdown retain the provenance of their mathematical inputs.

Throughout, `p` is prime and `F : PadicField.{uF} p`. The local normed-field
instance is exactly `F.canonicalNormedField`; thus the admissibility and
smooth-dual constructions use its canonical topology. A single representation
has carrier `V : Type uV`. For pairs, `V : Type uV` and `W : Type uW` are
independent of each other and of `uF`. Ranks are positive ranks `n + 1`
and `r + 1`, including rank one.

`SmoothDual π` is the Library's smooth subspace of the algebraic dual, with
action `smoothContragredient π`. The inverse-transpose pullback is a separate
representation on the original carrier. The new construction relates these
representations by an actual equivariant equivalence.

## Equivalences and Whittaker type

`inverseTransposeSmoothDualEquiv F π hadm hirr` has type

```lean
(inverseTransposePullback π).Equiv (smoothContragredient π)
```

Here `hadm : IsAdmissible π` and
`hirr : Representation.IsIrreducible π`. The construction chooses the linear
equivalence supplied by `gelfandKazhdanContragredient` and bundles its
pointwise equivariance using `Representation.Equiv.mk` and `LinearMap.ext`.
There is no prescribed normalization of this choice.

For any `UnitaryAdditiveCharacter ψ`, `smoothDualFunctionalEquiv` composes
`dualFunctionalEquiv π ψ` with `Langlands.Whittaker.functionalsCongr` for
the chosen equivalence. It gives

```lean
glFunctionals ψ n π ≃ₗ[ℂ]
  glInverseFunctionals ψ n (smoothContragredient π)
```

`smoothDualInverseFunctionalEquiv` makes the reverse-character construction,
from inverse-standard functionals on `π` to standard functionals on its
smooth dual. These are equivalences of the entire spaces, whether or not
those spaces are nonzero. Neither constructor requires genericity.
Continuity, unitarity, and nontriviality of `ψ` are already bundled in
`UnitaryAdditiveCharacter`.

Writing `E` for the chosen representation equivalence and `w` for the long
Weyl element, `smoothDualFunctionalEquiv_apply` proves the evaluation formula
`ℓ(π(w)(E.symm v))` for `v : SmoothDual π`. This equality is definitional
from the two composed transport maps.

`isOfWhittakerType_smoothContragredient` and its `_inverse` version transport
all three clauses of `IsOfWhittakerType`: admissibility, finite generation
over the group algebra, and a nonempty linear equivalence of the functional
space with `ℂ`. The source type supplies admissibility; irreducibility is a
separate hypothesis. The proofs first transport type through inverse
transpose and then use `IsOfWhittakerType.of_equiv`. The character changes
from standard to inverse-standard, or conversely.

## Polynomial relation and constructed L-factor

In the `Pair` section the field's measurable space is its Borel space. The
quotient measurable space and the quotient measure
`μ : Measure (LeftUnipotentQuotient n F.Carrier)` are supplied. So are the
additive Haar measure `ν`, the natural number `q`, and the absolute value
`abv`. The equivalence transport leaves all of these data fixed.

For admissible irreducible `π` and `σ`,
`isDualPairLPolynomial_iff_smoothContragredient` identifies

```lean
IsDualPairLPolynomial q ψ abv μ ν π σ P
```

with

```lean
IsPairLPolynomial q (ψ.scale (-1)) abv μ ν
  (smoothContragredient π) (smoothContragredient σ) P
```

The proof applies `isPairLPolynomial_congr_equiv` to the two chosen
equivalences. `dualPairLPolynomialExists_iff_smoothContragredient` then
transports the existential quantifier over `P`.

`smoothDualPairLFactor F hπ hσ hirrπ hirrσ h` transports the supplied proof
`h : DualPairLPolynomialExists q ψ abv μ ν π σ` to the actual smooth-dual
pair and applies `pairLFactor`. Its result is a unit in the rational-function
field. For any polynomial certified by the actual smooth-dual relation,
`smoothDualPairLFactor_eq` identifies its underlying rational function with
the reciprocal of that polynomial's image in `RationalFunctions`.
`smoothDualPairLFactor_eq_dualPairLFactor` proves equality of units with
`dualPairLFactor h`, using the source's chosen polynomial as a common
certificate and then unit extensionality.

The spectral convention is `X = q^(-s)`. The dual-pair character is
`ψ.scale (-1)`. The existing relation keeps every rank branch: all rectangular
blocks when `n < r`, the equal-rank integral when `r = n`, and `False` when
`r < n`. Accordingly, existence is an explicit input and supplies a common
normalized generator in the unequal-rank case.

## Symmetric p-adic relations and scope

The three theorems whose names begin
`isPadicSymmetricLPolynomial_inverseTranspose_iff_`,
`isPadicSymmetricEpsilonFactor_inverseTranspose_iff_`, and
`isPadicSymmetricGammaFactor_inverseTranspose_iff_` end in
`smoothContragredient`. Each replaces both inverse-transpose pullbacks by
the corresponding actual smooth contragredients in the named relation.
The proofs apply that relation's existing `congr_equiv` theorem to the
chosen equivalences.

These relations use `F.canonicalTopologicalData`, its residue cardinality
and normalized absolute value, and its compatible quotient measures.
Their topology agrees definitionally with the instance installed here.
The scalar additive Haar measure `ν`, supplied character `ψ`, and value
(`P`, `e`, or `G`) are unchanged. The caller may supply the reversed
character. The symmetric convention places the larger rank first and
covers either rank order.

No analytic existence, functional equation, classification theorem, or
unconditional total factor is proved here. The symmetric epsilon and gamma
results identify existing relations; they do not select epsilon or gamma
values. Full Whittaker type alone is never used to infer irreducibility.

## Development verification

The paired module compiled in environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` with zero errors and warnings in local
check `5c641c4c-a40a-44d2-be71-97b6d480e72e`. Check
`7b054af4-8ecc-4c14-9ed0-025cb3c809ac` compiled it with a private inspection
module, inspected the complete declaration types and the selected
constructor, and reported only `propext`, `Classical.choice`, and
`Quot.sound` as axioms. These development checks establish compilation;
independent semantic review and publication are separate steps.
