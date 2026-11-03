# The actual intersection quotient inside an ambient homogeneous quotient

Internal construction by Worker 1438 from the actual scheme-theoretic subgroup
intersection, exact all-test homogeneous quotient fibers, fpqc descent of
morphisms, and Mathlib pullback topology. This is a supporting unit for the
centralizer–Borel argument; it supplies no proof of the main statement.

For group schemes `M`, `B`, and `G` over an arbitrary base scheme `S`, let
`j : M → G` and `b : B → G` be actual homomorphisms. An actual quotient
`q : G → Q` is supplied whose fibers on every relative test scheme are exactly
the right cosets of `b`. Restricting `q` along a monic `j` gives exactly the
right-coset fibers of the actual first intersection projection
`subgroupIntersectionFst j b`.

When `b` is monic, the actual multiplication map `M × B → G`, together with
the first projection to `M`, is a pullback of `q` along `j` followed by `q`.
Its universal lift comes from the uniquely determined `B` point of the
right difference. Consequently its underlying image is exactly the inverse
image under `q` of the restricted quotient image. A smooth surjective `q`
is an open quotient map, so closedness of the actual product image makes
the restricted quotient image closed.

Supply also an actual fpqc quotient `r : M → R` whose all-test fibers are
the right cosets of the intersection. With `j` monic, the restricted map is
constant on those fibers and descends to `intersectionQuotientMap : R → Q`.
Pulling it back along `r` recovers `j` followed by `q`. Two fpqc local lifts
of quotient points, followed by the exact fiber criteria, prove this
comparison is monic. Surjectivity of `r` identifies its underlying image with
the restricted quotient image, hence with a closed subset whenever the
actual product image is closed.

The final implications retain an explicit `IsImmersion` premise for the
comparison. With this premise, its closed image makes it a closed immersion.
If `Q` is proper over `S`, composition then makes `R` proper over `S`.
This module does not prove the remaining immersion property, construct the
quotient models, prove product closedness unconditionally, or establish
Borel maximality. In particular, monicity and closed image alone are not
used to assert that the comparison is a closed immersion.
