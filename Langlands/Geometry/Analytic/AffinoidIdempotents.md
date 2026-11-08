# Units and the Shilov idempotent theorem for presented affinoid algebras

Author: Worker 36.

This module proves three facts for a presented affinoid algebra `A` over a
complete ultrametric field `K`. If the spectrum of `A` is empty, then `A` is
the zero ring. An element is a unit exactly when no point of the spectrum
vanishes on it. The clopen subsets of the spectrum correspond to the
idempotents of `A` (Shilov's idempotent theorem), and every clopen subset is
the locus of a rational chart. The proofs use the Library's finite descent
for algebras of affinoid domains, not the holomorphic functional calculus of
the source.

## Original source and derived provenance

The source is Berkovich, *Spectral theory and analytic geometry over
non-Archimedean fields* (1990), registered as
`provided-a03a0182668f6b92b01deacac09a9992b3edf55e23a0a2194554384ae44bd8d4`,
PDF SHA256 `9b543e7ffae8ec6febf154a60c4d11a288f7ecc3795c66f004ba3200a6824e79`.
The relevant original passages are:

- Theorem 1.2.1, printed p.13 / PDF p.27: the spectrum of a commutative
  Banach ring is a nonempty compact Hausdorff space;
- Corollary 1.2.4, printed p.15 / PDF p.29: "An element `f` of a commutative
  Banach ring `𝒜` is invertible if and only if `f(x) ≠ 0` for all
  `x ∈ 𝓜(𝒜)`";
- Theorem 7.4.1 (Shilov Idempotent Theorem), printed p.135 / PDF p.149: "Let
  `𝒜` be a commutative Banach k-algebra with identity, and let `𝒴` be an open
  and closed subset of `𝓜(𝒜)`. Then there exists a unique idempotent `e ∈ 𝒜`
  which is equal to `1` on `𝒴` and `0` outside `𝒴`."

The statements are transcribed for presented affinoid algebras only. The
source states them for all commutative Banach rings or algebras, which this
module does not treat. For affinoid algebras only the nonzero case of Theorem
1.2.1 is stated, in the contrapositive form `subsingleton_of_isEmpty`. All
proofs are derived. The source proves Theorem 1.2.1 by Zorn's lemma,
Corollary 1.2.4 by passing to quotients by maximal ideals, and Theorem 7.4.1
by holomorphic functional calculus. Here the proofs use the Library's descent
theorem for finite covers of affinoid domains
(`Domain.FiniteCover.algebra_existsUnique` and
`Domain.FiniteCover.algebra_ext_of_restrict_eq` in `DomainAlgebraGluing`), its
rational neighborhood basis (`RationalChart.exists_rational_neighborhood`)
and compactness of the spectrum. The rational chart of a clopen subset is
derived.

## Empty spectra

- `Domain.subsingleton_algebra_of_locus_eq_empty`: if a domain `U` has empty
  locus, the empty family is a finite cover of `U`. Restrictions along it
  detect equality, so any two elements of `U.algebra` are equal.
- `Domain.restriction_toWhole`: an inclusion into the whole-spectrum domain
  restricts by the structural map of the source domain. The structural map of
  the whole domain is the identity.
- `subsingleton_of_isEmpty`: an affinoid algebra with empty spectrum is the
  zero ring, by the first item applied to the whole-spectrum domain.

## Units

`isUnit_baseMap_lowerBound`: in the Laurent chart `q ≤ |a|`
(`RationalChart.lowerBound a q hq`) the image of `a` is a unit. The chart's
denominator class is `a` itself, and the Library proves that rational
denominators become units.

`isUnit_iff_forall_ne_zero`: `a` is a unit if and only if `x a ≠ 0` for every
point `x`.

- If `a u = 1`, then `x a · x u = 1` for every point `x`.
- Conversely, an empty spectrum makes `A` the zero ring. Otherwise the
  continuous function `x ↦ x a` attains a minimum `q > 0` on the compact
  spectrum. The Laurent chart `q ≤ |a|` then has the whole spectrum as its
  locus, so it alone is a finite cover of the whole-spectrum domain. Descent
  along this one-member cover glues the inverse of the image of `a` to an
  element `b` of `A`. The restriction of `a b` is `1`, and restrictions detect
  equality, so `a b = 1`.

## Idempotents and clopen sets

- `idempotent_apply_eq_zero_or_one`: a point takes the value `0` or `1` on an
  idempotent, since `x e · x e = x e`.
- `isClopen_setOf_idempotent`: the set where an idempotent `e` takes the
  value `1` is both `{x | 1/2 ≤ x e}` and `{x | 1/2 < x e}`, hence closed and
  open.

`exists_idempotent_of_isClopen` is Shilov's theorem for presented affinoid
algebras. Let `C` be clopen.

1. Each point has a rational chart whose locus is a neighborhood of the point
   inside `C` or inside its complement, both of which are open. By
   compactness, finitely many of these charts cover the spectrum.
2. They form a finite cover of the whole-spectrum domain. Take the family
   equal to `1` on charts inside `C` and `0` on the others. It is compatible.
   A domain mapping to a chart inside `C` and to a chart inside the complement
   has empty locus, so its algebra is the zero ring.
3. Descent glues the family to an element `e`. It is idempotent because its
   restrictions are. At a point `x` of a chart `d`, write
   `x = BanachSpectrum.comap d.baseMap y` (the represented locus is the image
   of the chart's spectrum). Then `x e = y (d.baseMap e)`, which is `1` or `0`
   according to the side of `d`.

`idempotent_unique_of_isClopen` proves uniqueness. For two such idempotents
`e`, `e'`, the element `w = (1 - e) - e'` vanishes at no point. On `C`,
`x (1 - e) = 0` and `x e' = 1`. Off `C`, `x e = x e' = 0` and `x 1 = 1`. So
`w` is a unit. Since `(e - e') w = 0`, `e = e'`. This is the source's argument,
with the unit criterion above.

## Definitions

- `IsClopenIdempotent C e`: `e` is idempotent, equal to `1` at the points of
  `C` and `0` at all other points.
- `clopenIdempotent C hC`: the idempotent of a clopen `C`, chosen by the
  existence theorem. `isClopenIdempotent_clopenIdempotent` records its
  property, and `IsClopenIdempotent.unique` says any two such idempotents
  agree.
- `isClopenIdempotent_setOf`: conversely, each idempotent is the idempotent of
  the clopen set where it equals `1`.
- `clopenRationalChart C hC`: the Weierstrass chart
  `RationalChart.upperBound (1 - e) (1/2)` for `e = clopenIdempotent C hC`.
  `locus_clopenRationalChart` proves that its locus is `C`. On `C`, the value
  of `1 - e` is `0`, since `(1 - e) e = 0` and `x e = 1`. Off `C`, it is at
  least `x 1 - x e = 1`. So every clopen subset of the spectrum is an affinoid
  domain, represented by a rational chart.

## Scope

The results concern presented affinoid algebras over a complete ultrametric
field, with no strictness, nontrivial valuation or reducedness assumption.
General commutative Banach rings, the holomorphic functional calculus and the
splitting of `A` as a product of Banach algebras (Berkovich's Corollary 7.4.2)
are not treated.
