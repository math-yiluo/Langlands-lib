# A finite central Frobenius kernel

Author: Worker 1487.

This module constructs an actual closed group scheme by intersecting a chosen
scheme-theoretic centre inclusion `z : Z ⟶ G` with the kernel of
`ρ ≫ GeneralLinear.frobeniusHom k p n`, for a matrix representation `ρ` of G.
The field `k : Type u` is arbitrary, and `n` is a small finite index type.
The intersection and finiteness work for every exponential characteristic p.
The tangent equality requires p greater than 1.

`CentralFrobeniusKernel.subgroup` is the actual pullback intersection and
`inclusion` is its inclusion in G. `range_eq` and `range_eq_of_center`
identify its point functor on every scheme test with the indicated intersection.
The inclusion is closed when z is closed, and it is central when z represents
the full centre. Its range is normal because conjugation fixes every central
point.

If ρ is a closed immersion, its composite with finite matrix Frobenius is
finite. The actual kernel pullback then proves that its kernel is finite over k.
The intersection projection to this kernel is a closed immersion, since z is
closed. Its composite with the kernel's finite structure morphism proves
`isFinite`. No smoothness of the centre, intersection or Frobenius kernel is
assumed.

For affine G and p greater than 1, `lie_eq_center` says that the tangent
submodule of the constructed range equals the tangent submodule of the full
centre on every commutative k-algebra A, including the zero ring. One inclusion
is immediate from the intersection description. For the other inclusion, the
proved zero differential of matrix Frobenius kills the image of every tangent
point under ρ. Thus every tangent point of the centre also lies in the actual
kernel used in the intersection.

`exists_subgroup` applies closed representability of fixed subgroups to the
self-conjugation action to obtain the full centre. It then uses the closed
linear embedding theorem for affine groups of finite type. These choices give
a finite central normal closed subgroup with the stated tangent equality for
every affine finite-type group over a field of positive characteristic.
The ambient group need not be smooth or connected.

This is an internal construction from actual closed subgroup intersections,
scheme-theoretic centres, closed fixed-subgroup representability, the closed
linear embedding theorem, finite matrix Frobenius, and its proved zero
differential. It does not prove existence of an isogeny quotient, a decrease of
geometric torus weights, torus lifting, or the parent no-torus theorem.
