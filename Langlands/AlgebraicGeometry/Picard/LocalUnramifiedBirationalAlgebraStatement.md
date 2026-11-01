# Local algebra for a birational unramified morphism

`Langlands.AlgebraicGeometry.LocalUnramifiedBirationalAlgebraStatement`
asserts the following local algebra result, in every universe. Let `R` be
a geometrically unibranch local domain. Let `A` be an actual `R`-subalgebra
of `FractionRing R` that is finite type and formally unramified over `R`.
If a prime ideal `q` of `A` lies over the maximal ideal of `R`, then
`A = ⊥`. The bottom subalgebra consists of the image of `R` under its
canonical injection into its fraction field. The prime-over condition
expresses nonemptiness of the closed fibre. This module only defines the
proposition.

This is a derived affine local consequence of Grothendieck and Dieudonne,
*EGA IV*, fourth part (1967), Remark 18.10.2(iii), printed pp.158–159, and
Lemma 18.10.18, printed pp.166–167. The registered source is
`grothendieck-dieudonne-ega-iv4-1967`, SHA256
`b4277fb99c6edf8feec5b01f54368e4b8521bcd52871316c0edf6ff4ae69389e`.
No source-specific project errata note was found; no correction to those
assertions was identified in the original List 3.

For this derivation from EGA, `Spec A → Spec R` is separated and locally of
finite type and has the same function field as `R`. The equality of
fraction fields follows because `A` contains `R` and embeds in its
fraction field. The cited results make this birational unramified map
an open immersion. Its image contains the closed point by `q`; every
open subset of the spectrum of a local ring containing the closed point
is the whole spectrum. The resulting isomorphism, with its displayed
map from `R`, gives exactly the bottom-subalgebra equality.

The intended independent algebraic proof uses algebraic Zariski's Main
Theorem and finite subalgebras of the canonical normalization. This is
an intermediate local target for `BirationalUnramifiedOpenImmersionStatement`;
passing to arbitrary scheme stalks and gluing local isomorphisms remain
separate obligations. No noetherianity, finite presentation or normality
assumption is included.
