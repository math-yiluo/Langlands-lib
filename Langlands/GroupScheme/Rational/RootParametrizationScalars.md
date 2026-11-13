# Scalar comparison of arbitrary root parametrizations

This internal unit extends the published comparison-isomorphism and torus-equivariance argument in `SteinbergRootMapUniqueness` from normalized simple-root maps to arbitrary supplied parametrizations of one intrinsic root subgroup. It uses `RootSubgroupAutomorphismRigidity` for coordinate linearity and `SteinbergModifiedRootProduct` for rational root points. It is derived infrastructure, with no direct literature assertion claimed.

Let `k : Type u` be any field, `G` an actual affine group scheme over `k`, `p` a supplied split pinning, and `x` and `y` supplied `RootParametrization`s of the same root. The isomorphism `comparisonIso x y` is the comparison between their two representations of the whole intrinsic root subgroup. Its composition with `y.hom` equals `x.hom`. The all-test torus-equivariance law makes this comparison equivariant under the full split torus. The published nonzero-weight coordinate-rigidity theorem therefore makes it coordinate-linear on every scheme test. In dimension one, its value at any coordinate `c` is `c` times its value at one.

`comparisonScalar x y : k` evaluates that comparison on the coordinate one over the base scheme and identifies its single global coordinate with an element of the original field using `Scheme.ΓSpecIso`. Scalar linearity and preservation of the map to `G` give, for every `c : k`,

`x.rationalPoint c = y.rationalPoint (c * comparisonScalar x y)`.

`comparisonScalar_ne_zero` proves that this scalar is nonzero: otherwise the identity at `c = 1` would identify the nonidentity point `x.rationalPoint 1` with the identity. This uses injectivity of the root parametrization and holds over finite and imperfect fields and in every characteristic; no argument on the density of rational points is used.

This unit compares root parametrizations only. It does not establish nonvanishing of a representation coefficient or the even-chain cross-section theorem.
