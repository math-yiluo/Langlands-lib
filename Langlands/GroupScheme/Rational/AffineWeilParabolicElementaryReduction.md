# From Weil parabolic–radical diagrams to elementary subgroups

Author: Worker 111.

The two theorems in this module are conditional consequences of the geometric
`AffineWeilParabolicRadicalTransportStatement.{u}`. They do not supply its
missing proof.

`affineWeil_parabolicUnipotentPointSet_image` proves that the published
equivalence `AffineWeil.rationalPointsEquiv k K G` maps
`parabolicUnipotentPointSet (AffineWeil.groupScheme k K G)` onto
`parabolicUnipotentPointSet G`. The generator sets use actual parabolic
inclusions and represented geometric radicals; the theorem retains all the
fields and hypotheses of the geometric statement.

In the forward direction, take a generator arising from `U → P → R_{K/k} G`.
The descent clause supplies `U' → P' → G` and isomorphisms `eU` and `eP`.
Functoriality of `AffineWeil.map` and the two commuting squares give

```text
eU.hom ≫ AffineWeil.map k K (r' ≫ p') = r ≫ p.
```

Map the radical rational point through `eU` and then through the published
point equivalence for `U'`. Naturality
`AffineWeil.rationalPointsEquiv_map` makes its image under `r' ≫ p'` equal
to the original generator's image.

Conversely, for an original diagram `U → P → G`, closedness gives affineness
of `P` and `U`, and their smoothness gives local finite type. These provide
the instances needed by `AffineWeil.map`. The preservation clause makes the
restricted arrows a parabolic–radical diagram. Apply the inverse rational-point
equivalence to the original point of `U`; its image under the restricted
composite is a generator over `k`. Naturality returns precisely the original
generator over `K`.

`affineWeilParabolicElementarySubgroup_of_radicalTransport` then unfolds the
definition of `parabolicElementarySubgroup`, applies
`MonoidHom.map_closure`, and rewrites by the generator-set equality. Its
conclusion is exactly the published
`AffineWeilParabolicElementarySubgroupStatement.{u}`. Its geometric premise is
explicit; the theorem makes no unconditional claim.

The provenance is internal composition of the stated geometric correspondence,
the published Weil map naturality and rational-point comparison, and subgroup
closure. Its source interpretation is documented in
`AffineWeilParabolicRadicalTransportStatement.md`. No local Kneser–Tits
statement or downstream consumer is used.
