# Degree-zero Tate normalization and transfer compatibility

Author: Worker 45.

`Langlands.Tate.ZeroLaws` is an exact proposition definition, not an assumed
theorem. It quantifies over every commutative scalar ring, finite group, and
representation in the arbitrary carrier universe `u` supported by Mathlib's
Tate interfaces. This includes the lifted integer scalar ring and its actual
trivial representation. No flatness or freeness condition is needed for
these degree-zero assertions.

The target asserts the following properties of the constructed operations.

1. Every actual degree-zero Tate class is represented by an invariant vector.
   Under `zeroEquiv` its class is the usual quotient class, and it vanishes
   exactly when the vector is in the range of the actual group norm.
2. The class map is natural for Mathlib's actual `tateCohomologyFunctor`.
3. The product of two invariant representatives is the class of their
   coefficient pairing. The product is natural for every commutative diagram
   of equivariant bilinear coefficient pairings.
4. For every subgroup, restriction is induced by inclusion of invariants,
   and corestriction is induced by the sum over left cosets. Their composite,
   corestriction after restriction, is multiplication by the subgroup index.
5. Restriction preserves the degree-zero product. Corestriction satisfies the
   projection formula with a restricted class in the second factor.
6. Both subgroup maps are natural in coefficients, using the actual Tate
   functors for the group and subgroup.

The subgroup need not be normal. The explicit finite enumerations of the
subgroup and coset space are available whenever the ambient group is finite.
The coefficient-pairing commutative diagram in item 3 is a hypothesis about
the supplied coefficient maps; none of the resulting cohomological
compatibility conclusions is assumed.

Sources: Jean-Pierre Serre, *Local Fields*, Greenberg translation, GTM 67
(1979), Chapter VII, §7, pp. 118–119 (PDF pp. 124–125); Chapter VIII, §§1–3,
pp. 127–132 (PDF pp. 133–138), especially the norm description, Tate
restriction/corestriction, and Proposition 5 degree-zero cup normalization.
Source `serre-1979-local-fields`, retained at
`C:/Central-Library/Serre--Local Fields--1979.pdf`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
The explicit comparison with Mathlib's complex and the coefficient-functor
naturality formulation are internal consequences of these constructions.

The constructions are imported from the published modules
`Langlands.Cohomology.Tate.ZeroDefinitions` and
`Langlands.Cohomology.Tate.ZeroTransferDefinitions`.
This target covers degree zero only. It does not claim
all-degree operations, subgroup transitivity, degree-minus-two comparison,
or compatibility with connecting homomorphisms.
