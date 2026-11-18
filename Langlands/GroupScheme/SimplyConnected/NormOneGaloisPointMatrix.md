# Galois intertwiners of the actual norm-one matrix representations

The matrix of the split norm-one representation on a scheme `T` over the
splitting field is read by its original algebra chart on the corresponding
point over the ground field. `chartBasePoint` is the map given by
`T`'s structure map to the splitting field, viewed over the ground field. The two constructions of the matrix
use the same extended algebra map on the actual tensor unit.

Changing the splitting-field structure of `T` along `Spec σ` retains
its ground-field test scheme up to the canonical descent identification.
Under the base-change point equivalence, the transported point is the
original point pulled back along this identification. The chart scalar
map is precomposed with `σ`, while the identification induces the identity
on global sections. The all-test chart equation then supplies the
intertwining equation for the actual representation's point matrices.
Applying inverse transpose to the group equality gives the corresponding
equation for the actual dual, with the inverse-transpose conjugator.

This is an internal deduction from the construction of the split norm-one
representation, the canonical base-change point equivalence and the
norm-one chart intertwining equations. It holds for every scheme test,
with the ground field, splitting field and original algebra in a common
arbitrary universe. The calculation applies to a separable-closure chart
without a finite-extension condition.
