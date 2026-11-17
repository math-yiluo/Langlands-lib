# Bernstein component sets of coefficient families

`Langlands.Renard.AlgebraicFamily.bernsteinComponentSet` names precisely
the set occurring in the published complex and coefficient-family
finite-type characterizations: the inertial classes supporting some
actual irreducible subquotient of the underlying smooth complex
representation. Irreducibility is included in the published
`IsBernsteinInertialSupport` predicate, and is not an extra premise.
The definition keeps the published standard-family data, canonical
point topology, affine and locally-of-finite-type hypotheses, local
compactness and nonarchimedean group premises, and the carrier universe
`max uF uV`.

The supporting theorems prove:

- An actual subquotient has its component set contained in that of its
  ambient representation, by transitivity of actual subquotients.
- A countable direct sum of actual subquotients of `A` has its component
  set contained in that of `A`. The implemented proof transfers each
  irreducible subquotient of the sum to one summand with the Library's
  `irreducibleSubquotient_directSum` theorem, then uses transitivity.
- If an actual complex subrepresentation spans a compatible coefficient
  family over `B`, it has exactly the same component set as the family.
  One inclusion uses the coefficient-span constituent-transfer theorem;
  the other uses the actual inclusion of the subrepresentation.

The preliminary `Langlands.SmoothRep.finite_asModule_of_irreducible`
records that an irreducible actual smooth complex representation is a
simple group-algebra module, hence finitely generated. It does not
assume admissibility.

Provenance: these are derived supporting definitions and lemmas for
David Renard, *Représentations des groupes réductifs p-adiques*, version
dated 9 July 2026, VI.10.7, Lemma, Proposition and Variant (printed
pp.215–217 / PDF pp.221–223), and the coefficient-family definition
VI.8.1 (printed p.187 / PDF p.193). The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The set is a name for the existing formulation, and the elementary
transport results are not attributed to separately numbered source
assertions. This unit proves no finite-type characterization and
assumes no unproved characterization.
