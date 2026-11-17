# The canonical sheaf of homogeneous cosets

This derived internal adapter starts with group schemes `H` and `G` over `S`
and a monomorphic subgroup map `i : H → G`. If `G → S` is locally of finite type
and `H → S` is smooth, `SmoothRelationQuotientProof` makes the canonical coset
presheaf an actual fppf sheaf and makes its quotient transformation smooth and
surjective.

The fiber-identification lemmas need only the monomorphic subgroup map: on
every scheme test, equality under the canonical quotient transformation is
equivalent to the two points differing by an element of the subgroup. The
group-valued base-change point equivalence identifies the restricted fibers
with cosets of the base-changed subgroup, without finiteness or smoothness
assumptions.

Under the locally finite type and smoothness hypotheses above, arbitrary base
change preserves the geometric properties of the quotient transformation.
Given an actual supplied `HomogeneousQuotient` of the base-changed subgroup,
its smooth surjective projection has the same fibers on every scheme test.
The fppf common-kernel recognition theorem then identifies the restricted sheaf
with the functor of points of that supplied quotient scheme. This recognition
is conditional on the supplied quotient.

All statements are derived from the imported quotient and base-change modules;
no additional literature assertion is introduced.
