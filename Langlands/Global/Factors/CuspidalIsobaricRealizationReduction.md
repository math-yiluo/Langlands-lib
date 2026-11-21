# Reduction of finite-place isobaric realization to constituent automorphy

`Langlands.Global.CuspidalIsobaricRealizationReductionStatement.{u, uQ}` is the
implication from `CuspidalInducedConstituentAutomorphyStatement.{u, uQ}` to
`CuspidalIsobaricRealizationStatement.{u, uQ}`. Both propositions use the supplied
cuspidal spectral presentations. The consequent realizes their local isobaric
sums at every finite place in one irreducible automorphic operator subquotient.

## Proof

`Langlands.Global.cuspidalIsobaricRealizationReduction` uses
`cuspidalIsobaricFiniteFamily` to obtain the family `A v` and a finite set `S`.
Each `A v` is an isobaric sum and a subquotient of the normalized block
induction. Outside `S`, it has a nonzero spherical fixed vector. Apply the
constituent automorphy premise to that family, its subquotient witnesses, and
its sphericity outside `S`. It returns one `Q` and an injective intertwiner
from each `A v` to the local restriction of `Q`. Pair these intertwiners
with the isobaric-sum and subquotient witnesses to obtain the consequent.

## Provenance

The implication isolates the last step of Getz–Hahn's proof of Theorem 10.7.5.
The local isobaric sums form a family of subquotients of normalized block
induction. Their sphericity outside a finite set permits application of
constituent automorphy to the entire family at once. The two Lean propositions
give the finite-place versions of these automorphy results.

| Registered source | PDF SHA-256 | Locator |
| --- | --- | --- |
| `getz-hahn-2024-automorphic-representations` | `a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507` | Theorem 10.7.1, pp. 286–287 (PDF 298–299), and proof of Theorem 10.7.5, p. 288 (PDF 300). |
