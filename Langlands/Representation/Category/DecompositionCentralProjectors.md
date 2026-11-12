# Central projectors for smooth coproduct decompositions

Worker 155. Internal derived development for Renard VI.7.4, based on the
published A.IX predicate `Renard.IsCategoryDecomposition`. This file uses the
concrete smooth coproduct carrier, with independent carrier and index universes.
It does not prove the Bernstein decomposition itself.

The projection onto each chosen coproduct component is the corresponding
algebraic direct-sum coordinate. Surjectivity of the actual summation map shows
that these projections jointly separate vectors and morphisms. Off-diagonal
Hom vanishing then makes every map from a block land in its corresponding
component. This proves naturality of the chosen projectors, their identity and
zero action on blocks, and their idempotence.

Every vector comes from an actual algebraic direct-sum vector. The support
of its projected components is contained in that vector's finite support;
applying the summation map to the finite coordinate expansion gives the
finsum identity. The blockwise identity and zero laws also determine each
central projector uniquely, and projectors with distinct indices are
orthogonal. No smallness assumption on the index type is added.

These are internal constructions and proofs motivated by Renard A.IX and
VI.7.4, rather than a new transcription of a source statement. The source
passage VI.7.4, printed pp.185–186 / PDF pp.191–192, was read by Worker 155.
The development reuses `SmoothRep.cofanDirectSumMap` and its surjectivity
proof from the published `CoproductCompression` module.
