# Uniqueness of solutions of birational group laws

`Langlands.AlgebraicGeometry.birationalGroupLawSolutionUniqueness` proves
`BirationalGroupLawSolutionUniquenessStatement` over an arbitrary scheme. It gives a unique
isomorphism of group schemes compatible with the solution embeddings on all pairs of test maps
with the same composite to `X`.

Let `U` be the intersection of the two open domains. This open is fibrewise dense in `X`, and its
images are fibrewise dense in both groups. The multiplication representative has smooth underlying
map, as it is the composite of its universal left translation, an open immersion, with the smooth
second projection. The open of pairs in `U ×_S U` where the representative is defined and takes
values in `U` is therefore fibrewise dense. The two solution laws agree there with the image of
this common product by their `mul_eq` fields.

`DenseGroupMultiplication.exists_hom_of_compatible_products` extends the comparison in each
direction by descending along multiplication on `U ×_S U`. The composites restrict to the identity
on the respective images of `U`. These images are schematically dense and the groups are
separated, so the two maps are inverse, and this also proves uniqueness. The test-map condition is
equivalent to agreement on `U`, since two maps with equal composites to `X` factor through the
intersection of their open domains.

The source is Bosch, Lütkebohmert and Raynaud, *Néron Models* (1990), §5.1 Proposition 3 and Lemma
4, printed pp. 113–114 (PDF pp. 120–121). The source ID is
`bosch-lutkebohmert-raynaud-1990-neron-models` and the file SHA-256 is
`16d0701b4192ae9db91d083c1df69c0492b00a994aee7bcb0abca365d859d529`. The formal proof uses the
kernel pair of the smooth multiplication cover for the extension step, where BLR invokes the
rational-map extension in §2.5 Proposition 5, printed p. 58 (PDF p. 65). The schematic-density
step corresponds to §2.5 Lemma 1(b), printed p. 56 (PDF p. 63).
