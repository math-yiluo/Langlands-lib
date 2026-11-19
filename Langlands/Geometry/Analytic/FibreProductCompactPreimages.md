# Hausdorff fibre products and compact preimages of compatible pairs

`projectionPair` is the continuous map from the glued fibre-product
quotient to the product of the two underlying factor spaces.

Hausdorff factors make the glued space Hausdorff. Points with different
projected pairs are separated by pulling back disjoint open subsets of
the product of the factors. Points with the same projected pair lie in
one open product patch over an open Hausdorff neighbourhood in the base.
The patch quotient is Hausdorff, and its open embedding carries
disjoint neighbourhoods into the entire quotient.

For a compact set of pairs whose base images coincide,
`isCompact_preimage_projectionPair` chooses a common open Hausdorff
base patch at each pair. The preimages in the factors admit finite
chart neighbourhoods. The rectangle of these neighbourhoods has
compact preimage in the glued fibre product, since each chart pair
decomposes into finitely many actual product charts over the base
patch. A finite subcover of the compact set of pairs covers its entire
preimage by those compact sets. The set of pairs is closed in the
Hausdorff product of the factors, so its preimage is compact.

These are internal consequences of the Library's saturated atlases,
finite pair-chart decomposition and open patch embeddings. They permit
compactness arguments on a product cut over an arbitrary ambient
analytic base.
