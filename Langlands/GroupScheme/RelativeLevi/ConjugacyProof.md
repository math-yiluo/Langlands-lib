# Unique conjugacy of relative Levi subgroups by the unipotent radical

Worker 593, with Worker 639's arbitrary-test uniqueness development.

`Langlands.GroupScheme.relativeLeviConjugacy.{u}` proves exactly the published
`Langlands.GroupScheme.RelativeLeviConjugacyStatement.{u}`. For every scheme
`S`, reductive group scheme `G/S`, relative parabolic `i : P ⟶ G`,
relative unipotent radical `r : U ⟶ P`, and relative Levi subgroups
`l : L ⟶ P` and `l' : L' ⟶ P`, there is a unique global point
`u : Over.mk (𝟙 S) ⟶ U.X` such that

```lean
SubgroupFunctor.range l' =
  SubgroupFunctor.range (l ≫ (P.innerIso (u ≫ r.hom.hom)).hom)
```

Thus the conjugation direction is `L' = u L u⁻¹`. Equality is equality of
subgroup functors on every relative test scheme, including nonreduced ones.
The base scheme and universe are arbitrary, and the theorem has no additional
hypotheses.

The implemented proof applies the published
`RelativeLevi.relativeLeviConjugacy_of_structuralStatements` to five published
whole-proposition proofs:

- `etaleLocalMaximalTorusExistence`;
- `etaleLocalMaximalTorusConjugacy`;
- `relativeTorusLevi`;
- `relativeUnipotentRadical`;
- `relativeLeviSelfNormalizer`.

The imported [synthesis](ConjugacySynthesis.md) first obtains maximal tori
étale-locally in each of the two given Levi subgroups and transports their
maximality to the parabolic. Étale-local conjugacy of those tori, followed by
uniqueness of the Levi containing a prescribed maximal torus, supplies actual
local ambient conjugating points with their all-test range certificates.

The relative radical theorem identifies the normal factor of a Levi
decomposition with the specified radical. Factoring each ambient conjugator
through that decomposition gives a local radical conjugator. Self-normalization
and the decomposition prove uniqueness on every test scheme. Consequently the
local radical points agree on scheme-theoretic overlaps and glue as actual
morphisms. Their all-test conjugacy certificates descend, and the base-section
comparison gives exactly the displayed subgroup-functor equality and uniqueness.
The present theorem discharges all five premises of that synthesis.

The provenance is internal composition of these Library proofs. The unchanged
[target statement](ConjugacyStatement.md) records its correspondence with
Conrad, *Reductive group schemes* (2014), Corollary 5.4.6, printed/PDF p.178,
and Definition 5.4.2, p.174. This theorem proves the unique-conjugacy assertion
for the two supplied Levi subgroups. Representability of the Levi functor and
existence of a global Levi subgroup are outside its conclusion.
