# Relative Levi conjugacy from structural statements

This internal synthesis proves that five complete structural propositions
imply the unchanged `RelativeLeviConjugacyStatement.{u}`. All five remain
explicit inputs:

- `EtaleLocalMaximalTorusExistenceStatement.{u}`;
- `EtaleLocalMaximalTorusConjugacyStatement.{u}`;
- `RelativeTorusLeviStatement.{u}`;
- `RelativeUnipotentRadicalStatement.{u}`;
- `RelativeLeviSelfNormalizerStatement.{u}`.

`relativeLeviConjugacy_of_structuralStatements` quantifies over every base
scheme and every group and inclusion in the published target. It applies
`etaleLocallyRangeConjugate_of_torusStatements` to obtain actual ambient
conjugating points on an étale cover. The earlier
`relative_existsUnique_conjugator_of_etaleLocal_range` then supplies the
unique global point in the specified unipotent radical.

That earlier reduction uses radical uniqueness to identify the normal
factor in a supplied Levi decomposition with the specified radical.
Factoring an ambient conjugating point through that decomposition produces
local radical conjugators. Self-normalization gives uniqueness on every
relative test scheme. This uniqueness supplies compatibility on overlaps;
the actual morphisms glue using the subcanonical topology, and their
all-test conjugacy certificates descend. The result has exactly the
conjugation direction and subgroup-functor equality of the published target.

`relativeLeviConjugatorFromStatements` uses classical choice on this
existence-and-uniqueness theorem to return an actual global radical point,
its conjugacy certificate, and a proof that every other such point equals
it. The base scheme is arbitrary and all objects lie in universe `u`.

The provenance is the composition of the local torus-cover construction and
the algebraic uniqueness and descent reduction. This module does not prove
any of its five structural inputs, and it is not an unconditional proof of
`RelativeLeviConjugacyStatement`.
