# Isomorphism from the three dynamic factors

This is a derived cell-comparison criterion for the final paragraph of Milne,
*Algebraic Groups* (2017), 23.18. It is internal infrastructure for the
Steinberg graph route to the split reductive isomorphism theorem.

Let p : D → G be a homomorphism of smooth connected affine group schemes
over any field k. Choose cocharacters χD and χG and actual representatives
of U(-χD), Z(χD), U(χD) and the analogous three target factors. Suppose
three actual group-scheme isomorphisms between the corresponding factors
commute with p and their inclusions. Then `isoOfTripleCellIsomorphisms`
constructs D ≅ G. Its forward map is p, as
`isoOfTripleCellIsomorphisms_hom` proves.

The compatibility equations are sufficient; the declaration does not need
an additional equation χG = χD ≫ p. In particular it applies to that
usual choice of the target cocharacter. The factors are full subgroup
functors represented on all schemes over k, not just on field points.

The implemented proof takes the product of the three given isomorphisms.
Naturality of triple multiplication identifies p composed with the source
cell with this product isomorphism followed by the target cell. Both cells
are open immersions, so p is monomorphic on the source cell. The cell
contains the identity, and smooth connected affine groups over a field
are geometrically integral. `OpenCell.iso` therefore applies once flatness,
surjectivity and quasi-compactness are established. For those properties,
the inverse factor isomorphisms put the three target dynamic factors in
the range of p, and `projection_geometry_of_contains_dynamicFactors`
supplies the required geometry.

The result does not construct the graph subgroup or the compatible factor
isomorphisms, and does not by itself prove the main split reductive
isomorphism statement. No restrictions on the characteristic, perfection
or algebraic closure of k occur.
