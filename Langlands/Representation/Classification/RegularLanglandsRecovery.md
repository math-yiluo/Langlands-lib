# Algebraic recovery from an actual block tensor equivalence

This module supplies two internal algebraic operations for assembling ordered
Langlands-data comparisons. It does not assert that equivalent Langlands
quotients give equivalent inducing representations.

`Langlands.GeneralLinear.BlockShape.eq_of_orderIso` identifies two block shapes
of the same total rank when an order isomorphism of their finite index sets
preserves every block size. Cardinality identifies their lengths. Every order
automorphism of a finite chain is the identity, so the two size functions agree.
The remaining fields of a block shape are propositions.

`Langlands.PadicField.TopologicalData.blockIsoOfTensorEquiv` has the following
inputs:

- a prime, a p-adic field with supplied topological data, and a block shape `B`;
- two families `σ` and `τ` of smooth complex representations of the corresponding
  general linear block groups;
- irreducibility of every factor in both families;
- an actual `Representation.Equiv` between the two external block tensor
  representations of `B.Levi`.

It returns, for each index `i`, an actual smooth representation isomorphism
`σ i ≅ τ i`. The field universe and the common universe of the factor carriers
are independent. There is no restriction on the total rank beyond the block
shape's own fields. At rank zero the family of outputs is empty.

For each index, the construction restricts the given tensor equivalence along
`MonoidHom.mulSingle`. The published
`Langlands.CuspidalSupport.external_mulSingle_tprod` identifies the restricted
actions on pure tensors with the actions of the chosen factors. Irreducibility
makes every source factor nontrivial, and the published
`Langlands.CuspidalSupport.nonempty_equiv_of_factor_actions` then supplies a
nonempty type of equivalences of the two factors. Classical choice selects one;
`SmoothRep.mkIso` bundles it as the requested smooth isomorphism. This selection
is not claimed to be canonical.

The provenance is internal: these are direct wrappers around finite-chain
rigidity and the published algebraic tensor-factor comparison, rather than
translations of a new assertion from the classification literature. In a future
application to Langlands data, equality of ordered ranks and exponents and the
required equivalence of the actual inducing tensor representations must still
be proved independently. This module imposes no temperedness or quotient
hypotheses and proves no classification or head-existence statement.
