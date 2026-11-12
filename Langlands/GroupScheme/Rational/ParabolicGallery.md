# Rank-one parabolic galleries with a fixed embedded Levi

This is an internal geometric interface for the persistence argument toward
irreducibility of induced unramified twists (Task 5515). It makes no
representation-theoretic assertion.

`IsRationalParabolicWithLevi j F` asserts that the subgroup functor `F` is the
image of an actual rational parabolic and that its specified rational Levi
has exactly the fixed composite embedding `j : L → G`.

`RationalRankOneWallData j F F'` gives an actual rational parabolic `P` of
`G` with rational Levi `M`, containing both vertices. Actual parabolics `Q`
and `Q'` of `M` are precisely the inverse images of `F` and `F'` under the
embedding `M → G`. Both have the original `L` as rational Levi, with equal
maps into `M` and composite `j` into `G`. Their intersection is precisely
that common Levi, on every scheme test; this is the opposite-parabolic
condition. The first inner parabolic is proper and maximal: any actual
rational parabolic containing it is either itself or all of `M`. This is
the geometric rank-one condition used here.

`HasRationalParabolicGallery` is the reflexive transitive closure of this
wall relation, with actual common-Levi witnesses at the endpoints. Thus it
is a finite chain, allowing length zero, and each intermediate vertex has
its own actual common-Levi witness.

For a specified torus map `b : B → L`, the restricted wall relation also
requires that `B` become noncentral in the intermediate Levi `M`. Its
reflexive transitive closure is `HasRationalParabolicGalleryAvoiding`.
When `B` is a central split subtorus of `L`, this condition expresses that
the wall root is nonzero on `B`. This interpretation motivates the name;
the formal definition is the displayed noncentrality condition itself.

The implemented elementary lemmas prove reflexivity, concatenation and
single-wall inclusion for ordinary galleries, reflexivity and
concatenation for restricted galleries, and forgetting the restriction.
They use the constructors and transitivity of `Relation.ReflTransGen`.
There is no gallery-existence theorem in this module.

The definitions are derived interface content, using existing actual
rational Levi and parabolic predicates, subgroup functors and their
inverse images. Opposite and maximality are written explicitly rather
than supplied as additional structural assertions. The proposed existence
proof will use a finite root-hyperplane argument and actual dynamic
parabolics; none of that proof is assumed by these definitions.
