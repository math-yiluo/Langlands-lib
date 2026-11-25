# Unequal-rank partial Whittaker factorization at one number field

Module `Langlands.Global.RankinSelberg.UnequalFactorizationAtStatement`, namespace
`Langlands.Global.RankinSelbergGlobal`. This module states five propositions; it proves none
of them. The field universe `u` and spectral-presentation universe `uQ` are independent.

## Fieldwise statements

`UnequalArchimedeanFactorizationAt F` and `UnequalPointwiseFactorizationAt F` have common
parameters `(F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]`.
Their bodies are those of `UnequalArchimedeanFactorizationStatement` in
[`ArchimedeanFactorizationStatement`](ArchimedeanFactorizationStatement.md) and
`UnequalPointwiseFactorizationStatement` in
[`ArchimedeanFactorizationReduction`](ArchimedeanFactorizationReduction.md), respectively,
after the field binders. Universally quantifying each fieldwise statement over its field and
these instances recovers the corresponding original proposition by definitional equality.
The original modules and declarations are unchanged.

Both bodies retain the unitary additive character `ψ` trivial on `F`, the ranks `t < r`,
actual cuspidal realizations and their contragredients, and spectral presentations with
irreducible admissible finite components. The set `S` still contains both exceptional sets
and satisfies `FiniteAdditiveSupport ψ S`. The real and complex components of `ψ` and
archimedean parameters of the four realizations, the canonical finite components `ψv` and
self-dual measures `νv` have their original specifications.

* **Integrated form.** It gives vectors spherical outside `S`, real and complex Whittaker
  functions and quotient measure data at infinity, and `PadicUnequalTestData` for the actual
  local components at `S`. On a right half-plane the ordinary and dual global partial
  integrals factor as the products of the corresponding infinite-place and `S` integrals,
  with the same nonzero constant `c`. Each of the two archimedean products and each of the
  two local integrals at every `v ∈ S` is nonzero somewhere in every right half-plane,
  with no requirement of a common witness.
* **Pointwise form (A_U at `F`).** It gives the same kinds of vectors, infinite-place and
  finite-place data, and a nonzero constant `κ`. For each `v ∈ S` and each `s`, the local
  functions `fS` and `gS` integrate to the ordinary and dual integrals of the test data.
  For every `s` on the classes `unipotentIntegralClasses F (t + 1) S`, the ordinary global
  integrand factors as `κ` times the product of the real, complex and `S` integrands at the
  quotient projections. The dual kernel factors with the same `κ`, using also the local
  rectangular coordinates and the indicator of integrality outside `S`. The same four
  nonvanishing clauses hold. There is no half-plane hypothesis on the pointwise identities.

The global partial integrals are declared in `PartialWhittakerIntegrals`; their integrands
`unequalWhittakerIntegrand` and `dualWhittakerKernel` are declared in `WhittakerIntegrals`.
`PartialIntegralExhaustion` declares `unipotentIntegralClasses`.
`ArchimedeanFactorizationReduction` declares the quotient projections, rectangular
coordinates, `rectIntegralOutside`, `padicQuotientIntegral`, `padicBlockIntegral` and the
`PadicUnequalTestData.quotientMeasure` accessor; `UnequalSemilocalFactorizationStatement`
declares `PadicUnequalTestData`. The predicates `IsRealPlaceWhittaker` and
`IsComplexPlaceWhittaker` come from `ArchimedeanPlaces`, and the local real and complex
integrands, kernels and integrals from `ArchimedeanIntegrals`.

The local affine and smooth scheme instances use the same `GroupScheme.GeneralLinear`
proofs as in the original modules. The module also gives local instance status to
`rectangleMeasurableSpace` and `rectangleBorelSpace` from `WhittakerIntegrals` and the real
and complex `Q`, `GL` and `N` measurable-space and Borel instances from
`ArchimedeanIntegrals`, as in `ArchimedeanFactorizationReduction`. They select the same
structures rather than imposing new premises; the canonical p-adic topology instances in
the `D` binders are retained as well.

## Totally complex statements

`UnequalArchimedeanFactorizationTCStatement` and `UnequalPointwiseFactorizationTCStatement`
quantify over `F` as above, adding `[NumberField.IsTotallyComplex F]` immediately after
`[NumberField F]`, and assert the corresponding fieldwise proposition at `F`. Nothing in
the bodies is changed: the real-place families are still indexed by the subtype of real
infinite places. On a totally complex field that index type is empty, so the real-place
requirements are vacuous and the real-place products are empty products. These restrictions
do not ask for factorization or nonvanishing tests at any field with a real place. They
still ask for the archimedean product nonvanishing and do not supply complex tests or their
functional equations.

## Fieldwise integration target

`UnequalArchimedeanFactorizationAtReductionStatement` says that for each number field `F`
with the same compactness instance, `UnequalPointwiseFactorizationAt F` implies
`UnequalArchimedeanFactorizationAt F`. No total-complexity assumption is needed for the
integration step. The existing `unequalArchimedeanFactorizationReduction` in
`ArchimedeanFactorizationReduction` only uses its pointwise premise at the output field
`F`. Its quotient and rectangular product premises are proved as
`unipotentClassProductStatement` in `UnipotentClassProductProof` and `rectangleTateStatement`
in `RectangleTateProof`. This new statement is a target for replaying that argument with a
premise at `F` alone. It is not obtained by simply applying the old theorem to a hypothesis
at only one field, and no proof of the new target is included. The unrestricted
factorization statements `ArchimedeanFactorizationStatement` and
`UnequalPointwiseFactorizationStatement` are unchanged.

## Provenance and source

Derived interface split for the totally complex route. The
integrated proposition formalizes the unequal-rank product step in J. W. Cogdell,
*Analytic theory of L-functions for GL_n*, in J. Bernstein and S. Gelbart (eds.),
*An Introduction to the Langlands Program*, Birkhäuser, 2004, pp. 197–228,
registered as `cogdell-2004-analytic-theory-gln`, proof of Theorem 4.1, printed pp. 219–220
(PDF pp. 222–223): the product of local integrals for suitable vectors at unequal ranks,
and the corresponding product on the dual side. Cogdell includes the infinite places in
his exceptional set; here `S` contains only finite places and the infinite product is
written separately. The pointwise premise, the split by field, and the separate fieldwise
integration target are Library interfaces, not separate assertions attributed to Cogdell.
The construction of the pointwise factorization and the semilocal functional equations
remain separate proof obligations.
