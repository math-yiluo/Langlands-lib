# The nilpotent and finite-field no-torus reductions

Author: Worker 1487.

`Langlands.GroupScheme.NoTorusBasicReductionStatement.{u}` packages two
conditional reductions used in the proof of `NoTorusUnipotentStatement`.
It is a proposition definition; this file supplies no proof.

Both clauses use the original no-torus hypothesis: every homomorphism
from every torus over the original field has trivial all-test range.
They use the existing representation-theoretic `IsUnipotent` predicate
and actual group schemes and inclusions. The universe is arbitrary.

## Nilpotent case

The first clause assumes `NilpotentCentralTorusStatement`. It concludes
unipotence for every smooth connected affine group scheme over any field
whose geometric point group is nilpotent and which has the stated
no-torus property.

The intended deduction applies the structural premise to obtain a
central maximal torus and an affine unipotent fppf quotient by its actual
range. The no-torus hypothesis makes this range trivial. An fppf quotient
with trivial kernel is an isomorphism, so unipotence transfers to the
original group. No perfectness, characteristic or cardinality condition
is imposed in this clause.

## Finite-field case

The second clause assumes `FiniteFieldGeometricMaximalTorusStatement`
and `AlgClosedTrivialMaximalTorusUnipotentStatement`. For every finite
field and smooth connected affine group scheme with the no-torus
property, it concludes unipotence.

The intended deduction chooses a torus whose actual algebraic-closure
base change is maximal. Its range is trivial over the original field,
so its base-changed range is also trivial. Connectedness persists under
field extension for the smooth connected affine group. The algebraically
closed structural premise gives unipotence after this extension, and
field reflection gives unipotence over the original field.

## Provenance and remaining obligations

This is an internal consumer statement for the published structural
interfaces. Its route follows the nilpotent and finite-field paragraphs
of Milne, *Algebraic Groups* (2017), Proposition 17.81, printed p.379
(one-based PDF p.395), source ID `milne-2017-algebraic-groups`.
The structural inputs retain their separate proof obligations: 16.47
for the nilpotent case, and 17.99 with 16.60 for the finite-field case.
The registered official errata snapshot does not change these passages.

The combined reduction leaves all three structural statements explicit.
It supplies no infinite-field nonnilpotent case, and proving it alone
does not prove the arbitrary-field parent target. In particular, its
finite-field route must not use preservation of maximal tori under field
extension or the parent no-torus theorem.
