# The actual rational support decomposition from three explicit inputs

Worker 4195. This module proves the exact Library proposition
`RationalSupportCategoryDecompositionStatement.{u, v}` (Renard, Théorème
VI.7.2, grouped by association classes of standard Levis) from three explicit
statement hypotheses. None of the three is proved here.

`rootAssociationSetoid i ν hN hZ` is the equivalence relation "some actual
representative `n` satisfies `rootAssociation i ν hN hZ I J n`" on the finite
sets of simple roots. Reflexivity, symmetry and transitivity are the published
`rootAssociation_one`, `rootAssociation_inv` and `rootAssociation_mul`.

`rationalSupportCategoryDecomposition_of_inducedCuspidal` takes:

* `hEmb : RationalCuspidalInducedEmbeddingStatement.{u, max (u + 1) v}`, the
  published finite induced-cuspidal embedding statement. It is used at source
  carrier universe `max (u + 1) v`, the carrier universe of the decomposition
  target. Its inducing and sum carriers are then also in
  `Type (max (u + 1) v)`.
* `hInd : RationalInducedCuspidalSupportCategoryStatement.{u, v}`, from the
  companion module `InducedCuspidalSupportCategoryStatement`: normalized
  induction of an inside-Levi cuspidal representation lies in `Alg({K})`.
* `hAssoc : RationalCuspidalSupportAssociationStatement.{u, v}`, the published
  association-of-cuspidal-data statement (Renard VI.5.4).

The proof introduces the binders of the target and fixes the finite simple-root
type with `simpleRelativeRootFintype`. It then applies the generic
`supportCategoryDecomposition_of_inducedEmbedding` with:

* the relation `rootAssociationSetoid i ν hN hZ`;
* invariance from the proved theorem `rationalSupportCategoryAssociationInvariance`.
  Its Levi-conjugation premise is supplied by the published
  `rootAssociation_levi_membership` from the displayed standard cocharacter
  premise;
* disjointness from the generic `exists_isAssociate_of_isInSupportCategory`,
  using `hAssoc`, the published `isLeviCuspidal_conjugation` and the
  association laws `rootAssociation_inv` and `rootAssociation_mul`;
* `hInd` and `hEmb` instantiated at the same binders.

The conclusion is the unchanged target at independent universes `u` and `v`.
It covers every connected reductive group scheme over every nonarchimedean
local field, positive characteristic, nonsplit and non-quasisplit groups, empty
simple-root sets and relative rank zero. The three inputs are stated with the
same structural telescope. No finite-length, admissibility, finite-generation,
endpoint or compact-limit premise is added. The transitive dependencies are the
three hypotheses above, together with the proved association invariance and
Levi-transport theorems already in the Library. No Langlands classification,
character independence or adjointness result is used directly. The geometric
lemma enters only through whatever later proves `hInd` and `hAssoc`.
