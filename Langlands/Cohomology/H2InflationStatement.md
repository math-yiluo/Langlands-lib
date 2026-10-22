# Degree-two inflation–restriction under degree-one vanishing

Author: Worker 10.

`Langlands.Cohomology.H2InflationRestrictionExactness` is a proposition
universally quantifying a commutative ring `k : Type u`, a group
`G : Type u`, a representation `A : Rep.{u} k G`, and a normal subgroup
`S : Subgroup G`, for an arbitrary common universe `u`. It states that
if `H¹(S, A) = 0`, then the sequence

`0 → H²(G/S, A^S) → H²(G, A) → H²(S, A)`

is exact at its first two cohomology terms. In Lean these conclusions are
injectivity of inflation and equality of its linear range with the
linear kernel of restriction. There is no surjectivity assertion for
restriction. Neither conclusion is an assumption.

All cohomology objects and maps are Mathlib's actual ordinary group
cohomology constructions. The short complex is
`groupCohomology.HInfRes A S 2`, imported from
`Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality`.
Its first object is the degree-two cohomology of
`A.quotientToInvariants S`, the quotient group's representation on the
`S`-invariants. Its middle object is `groupCohomology A 2`, and its last
object is `groupCohomology (Rep.res S.subtype A) 2`.
The map `.f` is induced by `QuotientGroup.mk' S` and the inclusion of
invariant coefficients into `A`; the map `.g` is induced by `S.subtype`
and the identity on the restricted coefficients. Their `.hom` fields
are the corresponding linear maps used in the range/kernel equality.

The vanishing hypothesis is
`Subsingleton (groupCohomology (Rep.res S.subtype A) 1)`.
This cohomology module contains zero, so being a subsingleton is
equivalent to every cohomology class being zero. It imposes exactly
degree-one vanishing for the restricted representation.
No finiteness, topology, triviality of the action, or field hypothesis
is imposed.

## Source correspondence

Jean-Pierre Serre, *Local Fields*, translated by Marvin Jay Greenberg,
GTM 67, Springer, 1979, Chapter VII, section 6, Proposition 5, printed
pages 117–118 / PDF pages 123–124. Registered source
`serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`,
retained at `/home/taskhub/central-library/Serre--Local Fields--1979.pdf`.
Worker 10 read these original pages and visually checked the displayed
sequence on printed page 117. No project errata entry for this source
was present when checked.

Serre's normal subgroup `H` is named `S` here. His proposition states
the degree-`q` sequence under vanishing in degrees `1` through `q − 1`;
the specialization `q = 2` has precisely the single hypothesis
`H¹(S, A) = 0`. The parenthetical sentence on printed page 118 explicitly
identifies this specialization.

Serre works with abelian groups equipped with a group action.
This statement is its scalar-linear reformulation: forgetting scalars
from a `k`-linear representation gives such a group module, and the
inhomogeneous cochains, differentials, inflation and restriction have
the same underlying additive maps. Their cohomology retains the
`k`-module structure. Consequently equality of the linear range and
kernel expresses the same underlying abelian-group exactness.
The commutative-ring parameter adds scalar structure to the source
formulation; it does not add an exactness hypothesis.

This file defines the proposition target only. Its proof is a separate
obligation, as is its specialization to finite Galois towers and the
comparison with their coefficient representations.
