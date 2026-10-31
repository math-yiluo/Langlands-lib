# The Harris rational Lie determinant through a single CM structure map

Author: Worker 57.

This internal construction combines `HarrisReflexBase` and
`LieRationalBaseIndependence` with the existing rational determinant
predicate. It makes both the actual Lie differential and the prescribed
coefficient sections use one CM structure morphism. No new theorem from
external literature is asserted.

Fix a totally real number field `E`, a totally complex quadratic extension
`F/E`, the displayed rational algebra structures and scalar towers, and
`D : CentralSimpleUnitaryData E F A n`. Fix an imaginary quadratic CM
number field `L` with `[Algebra L F]`, its complex embedding `τ₀`, and actual
Harris signature charts for `harrisCMSection E (algebraMap L F) τ₀`.
In particular, the section uses the same embedding of `L` into `F` as an
arithmetic trace formula using this algebra structure.

For an arbitrary actual scheme `S : Scheme.{0}`, fix
`p : S → Spec F`, an actual abelian scheme `B/S` and an actual rational
algebra action `i : A →ₐ[ℚ] End0 B`. No reducedness or flatness condition
on section rings is imposed. The existing construction gives the reflex
structure morphism `b := D.harrisReflexStructure C p` and the scalar map
`D.harrisReflexToCM C` from the actual cocharacter reflex field into `F`.
Neither a reflex-field equivalence nor a nonexceptional-rank hypothesis
is required.

`HarrisCMRationalLieDeterminantConditionAt` equates the polynomial of the
actual rational Lie action, supplied with rational scalars by `p`, with
the existing reflex polynomial first mapped into `F` by
`harrisReflexToCM` and then into the actual section ring by `secHom p`.
It quantifies through its arguments over any finite family in the
constructed Harris order, any actual finite free Lie chart on an open
`U`, and any smaller open `V : Over U`. Thus it is an equality of
multivariate polynomials over the full actual section ring.
The `_iff_coeff` theorem is precisely equality of every coefficient,
using multivariate polynomial extensionality and the coefficient map
formula.

`harrisCMRationalLieDeterminantConditionAt_iff` proves equivalence with
the previous local determinant condition at the constructed `b`. Its
proof uses fixed-scheme rational Lie base independence on the left and
the actual reflex-to-CM coefficient-section identity on the right.
The `_restrict` theorem transports the already proved smaller-open
restriction law through this equivalence.

`HarrisCMRationalLieDeterminantCondition` requires this identity for every
finite family, open, finite index set, actual Lie chart and smaller open.
The global `_iff` follows pointwise from the local equivalence.
The `_iso` theorem transfers the existing global invariance under an
actual two-sided equivariant rational isomorphism through that
equivalence. It does not assume geometric-dimension invariance.

These are derived compatibility results for the existing Harris
construction. They do not equate independent structure maps, assert the
determinant test automatically, compare it with the full Lie-plus
compatibility condition, prove scheme-base-change naturality of Lie
sheaves, or construct a representing scheme. The prescribed geometric
dimension and central trace condition remain additional tests.
