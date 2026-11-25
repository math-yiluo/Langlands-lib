# Actual residue data fixing a prescribed coefficient-fixed building point

Module `Langlands.Geometry.Building.UnramifiedFixedPointResidueData`.
This internal composition works at arbitrary universe `u` and in both
characteristics.

Keep the original Galois-stable maximal-unramified apartment, actual
centralizer, full omega compatibility and extended connected reductivity.
Assume geometric connectedness of the original group, as supplied by its
original connected reductivity in the statement this module serves. For every prescribed
coefficient-fixed point `y` of the original reduced quotient,
`UnramifiedFixedPointResidueDataStatement` constructs:

* A maximal original Galois facet `E` whose combinatorial fixed closure
  contains `y`, and one translated apartment containing `E` and that closure.
* An actual downstairs full/neutral model pair recovering the constructed
  upper facet model at `E`, and valid reductive quotient data `Q0`.
* Containment of the actual unramified neutral integral-point subgroup in
  the full fixer of the original prescribed point `y`.
* Absence of proper rational parabolics in `Q0.quotient`, and centrality and
  maximal-torus containment for all its maximal split tori.

`unramifiedFixedPointResidueData` proves this Prop-valued statement. All
models and residue geometry are constructed. It does not assume a model
fixing `y`, an image bijection or quotient covariance.

## Implemented proof

The published `exists_maximal_galoisFacet_apartment` chooses `E` above the
full facet of `y`, proves maximality and fixed-closure membership, and
supplies the translated apartment. Apply
`constructedMaximalGaloisFacetResidue` to this same `E` to construct the
recovered lower models and actual residue quotient with the two algebraic
consequences.

The published equality `galoisFacetClosure_eq_inter` puts `y` in the
original upstairs combinatorial closure. The published
`pointwiseFixer_buildingFacetClosure` identifies the whole-facet and
closed-facet pointwise fixers. Consequently the full pointwise fixer of
`E` fixes `y`. The constructed upper neutral-model integral points are the zero subgroup
intersected with that fixer. Actual identity-generic model recovery
identifies them literally with the unramified integral-point subgroup of
the chosen lower neutral model.
This proves the required fixation containment inside the original
rational-point group and the original quotient action.

The next split-source lifting step may therefore use this lower neutral
model's actual quotient and the exact prescribed-point fixer containment.
The existence of a compatible integral split source with an `F`-maximal
generic inclusion, and the final torus lift and unit-fixation conclusion,
are not proved here. No rank assertion about arbitrary smooth models or
containment of an `F`-maximal split torus in the arbitrary originally
supplied `K`-maximal torus is assumed. The proof uses the actual-model
constructions imported through `ConstructedMaximalGaloisFacetResidue`, without
building descent.
