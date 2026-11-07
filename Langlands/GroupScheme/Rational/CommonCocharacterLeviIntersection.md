# Actual Levi intersections for supplied common cocharacters

This internal construction works over an arbitrary field. Let two supplied
cocharacters of a common commutative group `T` map to an ambient group `G`,
and let a closed map `j : M → G` represent the first dynamic centralizer on
every relative scheme test. Assume that `M` is connected reductive. The theorem
`exists_leviIntersection_of_commonCocharacters` constructs an actual parabolic
of `M`, a rational Levi, and its complementary full geometric unipotent radical.
Their ambient ranges are respectively the intersections of `range j` with the
second dynamic parabolic, centralizer and identity-limit subgroup. It also
factors the original map from `T` through the constructed common Levi.

`CommonCocharacterLeviIntersection` packages these actual schemes, maps,
structural proofs, intersection identities and factorization.
`commonCocharacterLeviIntersection` chooses such a package from the proved
existence theorem using classical choice.

The proof uses `Dynamic.intersectionCocharacter` to restrict the second
cocharacter to the first centralizer. Its three dynamic subgroup functors are
the exact preimages of the ambient ones. The existing affine decomposition
model supplies the actual schemes, closed inclusions and multiplication
isomorphism. The proved dynamic parabolic recognition, centralizer reductivity
and geometric unipotent radical results supply all structural assertions.
The geometric radical comparison over field extensions yields the radical
predicate required by the rational-Levi interface. Mapping the three preimages
through `j` yields the three stated all-test intersection identities. Points
of `T` centralize both cocharacters because `T` is commutative, so the
represented common Levi supplies the final factorization.

The provenance is internal: this specializes and completes the supplied-
cocharacter part of `ParabolicLeviIntersectionReduction` using published
structural proofs. It adds no universal parabolic-dynamic or centralizer
reductivity hypothesis. It does not choose cocharacters for arbitrary supplied
parabolics, prove finite double cosets, or establish a representation-theoretic
geometric lemma.
