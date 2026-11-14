# Assembly of the spherical L-factor generation facts

Author: Worker 8. The module proves the published
`Langlands.Conductor.SphericalLFactorGenerationStatement`
([`SphericalLFactorGenerationStatement`](SphericalLFactorGenerationStatement.md))
from one statement, which is not proved here or elsewhere in the Library:

```lean
theorem sphericalLFactorGeneration_of_generation
    (hgen : OrderedUnramifiedCorankOneGenerationStatement.{uF, uV}) :
    SphericalLFactorGenerationStatement.{uF, uV}
```

`hgen` is Jacquet 2012, Lemma 3, for norm-ordered parameters
([`OrderedUnramifiedCorankOneGenerationStatement`](OrderedUnramifiedCorankOneGenerationStatement.md)):
for norm-ordered `x` and a nonzero inverse-character functional on `I(x)`, a
finite sum of corank-one integrals of `π × I(x)` times `∏_i P(x_i q^(-s))` is
`1` on a right half-plane. Jacquet takes it from JPSS 1983, Theorem (9.4).
The theorem is conditional: it does not prove
`SphericalLFactorGenerationStatement` until `hgen` is proved.

## The proof

One application of the published `sphericalLFactorGeneration_of_ordered`
([`SphericalLFactorGenerationReduction`](SphericalLFactorGenerationReduction.md)),
whose other four premises are proved:

- the convergence statement, by `sphericalCorankOneConvergence`
  ([`SphericalCorankOneConvergenceProof`](SphericalCorankOneConvergenceProof.md));
- the Laurent statement, by `unramifiedCorankOneLaurent`
  ([`SphericalCorankOneLaurentProof`](SphericalCorankOneLaurentProof.md));
- Jacquet's Lemma 1, by `orderedUnramifiedSphericalCyclicity`
  ([`OrderedUnramifiedSphericalCyclicity`](OrderedUnramifiedSphericalCyclicity.md));
- Jacquet's Lemma 2 with the normalization of the spherical image, by
  `orderedUnramifiedWhittakerRealization`
  ([`OrderedUnramifiedWhittakerProof`](OrderedUnramifiedWhittakerProof.md)).

`hgen` is passed through.

## Source

H. Jacquet, *A correction to Conducteur des représentations du groupe
linéaire*, Pacific J. Math. 260 (2012), 515-525, literature ID
`jacquet-2012-conductor-correction`, section 1, printed pages 517-519, and
H. Jacquet, I. I. Piatetski-Shapiro, J. A. Shalika, *Rankin-Selberg
convolutions*, Amer. J. Math. 105 (1983), 367-464, literature ID
`jpss-1983-rankin-selberg`, Theorems (2.7), (3.1) and (9.4). The module only
combines the results described in the linked files.
