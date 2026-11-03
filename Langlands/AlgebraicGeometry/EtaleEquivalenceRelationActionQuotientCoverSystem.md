# Finite type quotient systems from two finite invariant covers

This internally derived construction combines the published action-diagram,
diagonal-pair, invariant affine quotient-cover descent, quotient gluing and
finite-type system constructions. Its geometric provenance is the proof of
Stacks Project, Proposition 70.8.1, Tag 07SU, in registered source
`stacks-noetherian-approximation-2026-11-01`: construct levels by base change,
form their quotient relations, and retain cartesian squares and the inverse
limit on object schemes. The simultaneous choice of two covers is internal
packaging for the first-level induction, rather than a separately stated result
in that source.

`ActionDiagram.finiteTypeCartesianSystemOfCovers` works in arbitrary universe
`u`. It takes a cofiltered diagram `D` whose object and arrow schemes are affine,
an action diagram `A` with affine points of finite type over the terminal
scheme, and an action cone `T` above an object-limit cone `c`. It also takes
finite invariant affine quotient covers of the action relation of `T` and of
its diagonal pair action, actual scheme quotients `Qc` and `Q₂c` of those two
relations, and a cartesian comparison `φ` from a supplied relation `E` to
`T.action.quotientRelation Qc Q₂c` whose object map is an isomorphism.
It produces the existing `FiniteTypeCartesianSystem E` structure.

The proof first obtains affineness of both action-relation diagrams from
affineness of the point and base schemes. The two supplied covers descend
independently by the published cover descent theorem; a common predecessor of
their indices exists by cofilteredness. Over the category of levels above that
predecessor, the pulled-back covers give actual scheme quotients at every
level. Their quotient maps are affine by the invariant-cover gluing theorem.
The point schemes remain affine and of finite type; their pair schemes are
affine and hence quasi-separated. The object cone remains a limit after
restriction to this category. The published
`ActionDiagram.finiteTypeCartesianSystem` then supplies all fields, including
the object-limit property, cartesian comparison, finiteness, separated source
and affine transitions.

No finite cover or quotient at a finite level is assumed. The only covers
supplied are on the two actual action relations at the limit. This result
retains the displayed affine, finite-type, cone-limit and comparison inputs;
applying it to the actual tuple action is a further step of the full
Noetherian first-level proof.
