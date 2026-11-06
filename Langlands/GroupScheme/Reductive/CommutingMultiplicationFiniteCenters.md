# Commuting multiplication with finite factor centres

Authors: Worker 1616 and Worker 1783.

This internal construction starts with two closed subgroup inclusions whose images commute on every relative test scheme. Over any scheme base with separated ambient group, finite full scheme-theoretic centres of both factors imply that the actual full multiplication kernel is finite over the base. The kernel inclusion is closed because the ambient target is separated, and is central by the multiplication-kernel calculation. The product has finite full centre by the actual product-centre theorem. Factoring the closed central kernel through that finite centre proves its finiteness, retaining its infinitesimal structure.

Over an arbitrary field, when the ambient group is smooth and affine and multiplication is scheme-surjective, the finite-kernel central-isogeny adapter now proves that the actual commuting multiplication is a central isogeny. There is no separate kernel-finiteness hypothesis and no smoothness hypothesis on either factor for this conclusion.

If the ambient group is semisimple and the two factors are smooth and connected, their actual product is semisimple. Closedness in the affine ambient group gives affine factors. The smooth-product theorem supplies source smoothness; the smooth-connected-affine geometry theorem supplies geometric integrality of the product, hence connectedness over the one-point field spectrum. Semisimplicity then follows from the published theorem transferring it to the smooth connected source of a central isogeny.

`semisimpleCommutingMultiplication` bundles the actual multiplication map with its central-isogeny property and the semisimplicity of its product source under these hypotheses. Its value theorem identifies the map with `commutingSubgroupMultiplicationHom`. This unit does not construct a complement, prove scheme-surjectivity of multiplication, or prove semisimplicity of either factor.

Provenance: internal composition of the all-test multiplication-kernel centrality, actual full product centre, finite closed central subgroup, finite-kernel central-isogeny, smooth-product geometry and semisimplicity-transfer results. No structural complement or root-theoretic assertion is assumed.
