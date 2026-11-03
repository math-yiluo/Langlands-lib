# Locally preserved measure on a finite character quotient

This is a derived measure construction supporting Waldspurger,
*La formule de Plancherel pour les groupes p-adiques (d'après
Harish-Chandra)* (2003), VI.3, printed p.302 (PDF p.68). That passage
equips a unitary unramified discrete-series orbit with the measure locally
preserved by its character parameterization. The character measure has
already been fixed in I.1, printed p.239 (PDF p.5): the split-center
character group has Haar mass one, and restriction from the group's
character group locally preserves measures. The latter character group
need not have mass one.

The Lean construction here is for a general commutative topological
group and a finite subgroup. The factor counting the finite fibers is an
internal derivation of the local-preservation convention; the article
does not state this pushforward formula explicitly.

## Data and local-preservation predicate

`IsLocallyMeasurePreserving f lambda mu` is a Prop-valued definition.
Every source point must lie in an open set on which `f` is injective.
Every measurable subset of that open set must have a measurable image,
and its image's `mu` measure must equal its `lambda` measure. This
predicate does not assert a global measure-preserving pushforward.

Let `C` be a commutative topological group and `S : Subgroup C` finite.
Use the usual quotient topology on `C / S` and Borel measurable spaces
on both groups. The projection is `q = QuotientGroup.mk`. The definition
`finiteCharacterQuotientMeasure S lambda` is

\[
  \mu_S = |S|^{-1}\,q_*\lambda.
\]

It accepts an arbitrary supplied measure `lambda`. The local-preservation
theorem additionally assumes `T2Space C` and left invariance of `lambda`.
No compactness, second countability, local compactness, nonzero measure,
probability condition or abstract Haar existence theorem is needed.
In particular the result applies to a chosen Haar measure with its
existing scale. Commutativity supplies normality of `S`.

## Construction laws and implemented proof

`finiteCharacterQuotientMeasure_apply` evaluates a measurable quotient
set `E` as `|S|⁻¹ * lambda (q ⁻¹' E)`.
`finiteCharacterQuotientMeasure_univ` gives the total mass
`|S|⁻¹ * lambda univ`.
`finiteCharacterQuotientMeasure_smul` proves that multiplying `lambda`
by any extended nonnegative scalar multiplies the quotient measure by
that same scalar. These laws preserve all scale information from I.1.

The two private set lemmas identify `q ⁻¹' (q '' E)` with the union of
the sets `h • E` for `h : S`, and prove those translates pairwise disjoint
when `q` is injective on `E`. For
`finiteCharacterQuotientMeasure_image`, `E` is measurable, `q` is injective
on it and its image is measurable. Left invariance makes each translate
have measure `lambda E`. Additivity over this finite disjoint union gives
`|S| * lambda E` for the full inverse image. The positive finite cardinality
of the subgroup cancels the reciprocal factor, including when
`lambda E` is infinite.

`isLocalHomeomorph_finiteCharacterQuotient` uses the discreteness of a
finite subset in a Hausdorff space and Mathlib's subgroup quotient
covering theorem. It requires only the topological group, finite
subgroup and Hausdorff hypotheses. A local homeomorphism supplies the
open injectivity charts. Its restriction to each chart is an open
embedding and hence a measurable embedding for the Borel measurable
spaces. Thus every measurable subset of a chart has measurable image.
Applying the preceding image formula proves
`isLocallyMeasurePreserving_finiteCharacterQuotient`.

## Scope and remaining comparisons

This pair supplies the finite-quotient measure and its construction laws.
It does not identify `C` with the source's actual unramified character
group, prove stabilizer finiteness, construct a split component or its
restriction map, or choose the character Haar scale of I.1. Those data
and their mathematical realization remain necessary for the intended
application. Transport of this measure to the existing actual
discrete-series twist orbit and independence of its base representation
are separate constructions. No smooth structure, coefficient family,
wave packet, density, formal degree, spectral finiteness or Plancherel
identity is claimed here.
