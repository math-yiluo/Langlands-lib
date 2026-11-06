# Actual torus cocycle trivialization from the norm criterion

This derived construction takes an arbitrary field `k : Type u` satisfying
`HasDimensionLEOne k`, an actual torus `T` over `k`, and an actual scheme
cocycle on any finite Galois field cover `L/k` in the same universe. It
constructs a trivializing point over that original cover. No splitting
assumption on `T_L`, perfectness, or characteristic restriction is supplied.

`IsTorus.cocycle_isTrivial_of_dimensionLEOne` first applies the proved finite
Galois splitting theorem to `T_L`. This gives a finite Galois extension `N/L`
that splits the torus. Composing the field maps makes `N/k` finite and
separable. The scalar-tower comparison identifies the split iterated base
change with the scalar extension of the original group scheme to `N`.
Embedding `N` into `SeparableClosure k` and taking its normal closure gives
a finite Galois extension `E/k`, containing the given `L` through `N`.
The compatible `L`-algebra structure on `E` makes `E/L` finite Galois as
well. Splitting propagates from `N` to `E`.

The actual torus is affine by the existing affineness-descent result and
commutative by the existing faithfully flat reflection of commutativity.
The proof therefore views the same group scheme as a commutative group
scheme and refines the original cocycle to the cover `Spec E`. The
splitting-cover vanishing theorem, using the original norm criterion on
`k`, trivializes that refined cocycle. The finite Galois refinement descent
theorem then produces triviality on the original cover `Spec L`. Its
fixed-point descent supplies the original-cover point, and the finite-Galois
value criterion supplies the coboundary identity on every relative test
scheme.

`IsTorus.cocycleTrivializingPoint` chooses that actual point. Its
`cocycleTrivializingPoint_spec` is the all-test coboundary identity given by
the proved existential. This is a derived combination of finite Galois
torus splitting, scalar-tower transport, the normal-closure construction,
the norm-based splitting-cover vanishing theorem, and actual point descent.
The structural passage from torus cocycle vanishing to quasi-splitness of
arbitrary connected reductive groups remains a separate obligation.
