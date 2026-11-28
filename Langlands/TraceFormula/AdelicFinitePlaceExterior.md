# The exterior factor of a restricted adelic tensor

`AdelicFinitePlaceExteriorStatement` concerns a restricted adelic tensor on an
affine group scheme over a number field. Its exterior function at a finite
place in the distinguished set is the product of the other designated local
factors, with the same integrality condition outside the distinguished set.
Inserting a local point at the removed place fixes every coordinate entering
that function. Splitting the finite product at the removed place lets two
tensors differing only there share one exterior function.

`localFactor_ne_zero_of_normOnePositiveAverage` takes a split torus over the
number field and a function already expressed as the distinguished local factor
times an exterior function. The intrinsic positive subgroup of the split
torus acts trivially on the distinguished finite coordinate. If the local
factor vanishes at the finite coordinate of a norm-one point, the integrand
vanishes pointwise for any measure on the intrinsic positive subgroup.
