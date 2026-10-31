# Full Whittaker-type unequal-rank bilinear uniqueness

This module proves
`Langlands.RankinSelberg.unequalRankBilinearUniqueness.{uF,uV,uW}`.
Its type is exactly the published
`UnequalRankBilinearUniquenessStatement.{uF,uV,uW} F T n r`
for every prime parameter, `F : PadicField.{uF} p`, supplied
`T : F.TopologicalData`, and natural numbers `n,r`. The field and both
representation-carrier universes remain independent.

The theorem retains the full `IsOfWhittakerType` hypotheses and every
specified standard and inverse-standard Whittaker functional, including
zero functionals. For all `n < r`, outside a finite set of spectral values
`q^(-s)`, every covariant bilinear form on the actual coefficient models
is a scalar multiple of any specified nonzero covariant form. The
exceptional set precedes `s` and both forms. The determinant exponent is
`(r-n)/2-s`, and the additional covariance uses the actual subgroup
`U_(n+2,r+1)`. The boundary cases `n = 0` and `r = n+1` are included.

## Unconditional source bound

The companion theorem `unequalRankSourceLengthBound` proves exactly
`UnequalRankSourceLengthBoundStatement.{uF,uV,uW} F T n r`.
It applies the published
`UnequalRankAssembly.sourceLengthBound_of_statements` to three proved
inputs:

1. `Whittaker.mirabolicFiniteLength.{uF,uV}` in
   `Whittaker.MirabolicFiniteLengthProof` proves finite length of the
   actual mirabolic restriction of a smooth finite-length general
   linear representation, for the supplied topological data.
2. `unequalRankMirabolicPairingRigidity.{uF,uV,uW}` in
   `RankinSelberg.UnequalRankMirabolicPairingProof` proves the exact
   irreducible source rigidity statement. Away from its finite
   exceptional set, a nonzero actual covariant form forces the first
   factor to be equivalent to the compact mirabolic model and gives a
   nonzero inverse-standard functional on the second factor.
3. `unequalRankCompactGenericPairing.{uF,uW}` in
   `RankinSelberg.UnequalRankCompactGenericPairingProof` proves that the
   actual compact/generic pairing space is linearly equivalent to `ℂ`
   for every exponent.

These are theorem applications; no source input remains a premise of
either new theorem.

The reused source assembly derives finite length of the original general
linear representations from their Whittaker-type hypotheses and applies
the first theorem to the first representation's mirabolic restriction.
The second representation stays on its original general linear group.
The separate-group functional-factor assembly then uses finite simple
filtrations and the one-dimensional total functional spaces. Its first
irreducible factors are smooth, and its second factors are admissible.
Admissibility of the second factors comes from that of the original
representation through the actual subobjects and quotients, using the
published compact-open cofinality result.

For each irreducible pair, nonzero mixed length gives a nonzero actual
source form. Rigidity identifies its first factor with the compact
model, and compact evaluation supplies that factor's nonzero
functional. Transporting the form space along this equivalence and
using the compact/generic theorem bounds its length by one. Zero pair
length already satisfies the bound. The functional-factor assembly
combines the finitely many pair exceptions before the varying
parameter. The published `UnequalRankMixedAdapter` identifies this mixed
length with the length of `unequalRankMirabolicForms` on the original
carriers, preserving both covariance laws.

The resulting source exceptional set is chosen even before any
coefficient-model functional. It therefore supplies the exceptional set
in the parent statement for every specified pair of functionals.

## Descent to coefficient models

`unequalRankBilinearUniqueness` applies the published
`UnequalRankAssembly.unequalRankBilinearUniqueness_of_source_length`
to the unconditional companion bound. That descent pulls a model form
back along the two actual `Whittaker.modelMap` intertwiners. Both maps
are surjective onto their coefficient images, so pullback is injective
and preserves the determinant and unipotent covariance laws.

Length at most one of the source form space implies proportionality to
any nonzero source form. Injective linear pullback carries this
proportionality back to the coefficient models. The descent also covers
specified zero functionals: their coefficient image is zero, so there
is no nonzero bilinear form on those images.

## Provenance

This is an internal extension of the irreducible generic Proposition in
Jacquet, Piatetski-Shapiro and Shalika, *Rankin-Selberg Convolutions*
(1983), Section 2.11, printed pp.398–403. Registered source:
`jpss-1983-rankin-selberg`, SHA256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Those six pages were read completely from the retained scan
(one-based PDF pages 33–38). No applicable registered erratum was found
in the checked project notes, Library notes/wiki and literature index.

With source ranks `R=r+1` and `t=n+1`, the printed Proposition's twisted
bilinear parameter is `λ=s-(R-t)/2`. Its untwisted covariance exponent
is therefore `(r-n)/2-s`, as in the unchanged target.
The Proposition and its mirabolic Lemma on p.399 assume irreducibility;
their proof on pp.400–403 uses distributions and support induction.
The present final module reuses the separately proved exact source
theorems and the finite-length functional-factor assembly to extend
uniqueness to all Whittaker-type data. It does not treat the printed
Proposition as already having that scope. The implemented final step
is algebraic assembly and coefficient descent; it does not reimplement
the distribution proof.

The result concerns uniqueness of covariant forms. Continued-integral
bilinearity and covariance, the construction of gamma factors and the
functional equation remain separate results.
