# Affine tensor comparisons for geometric irreducibility spreading

These are internal comparison lemmas for the arbitrary-scheme
spreading proof. They use Mathlib's actual scheme pullbacks and residue-field
fibres, and do not assume a spreading theorem.

The first comparison identifies irreducibility of an affine pullback with
primality of the nilradical of the tensor product, using the pullback symmetry,
Mathlib's pullbackSpecIso, and the prime-spectrum irreducibility criterion.
The second comparison quantifies this over every field algebra, giving exactly
the geometric irreducibility condition for an affine scheme morphism.

The generic-fibre comparison starts with the actual scheme-theoretic fibre at
the prime nilradical. Mathlib's fibre arrow isomorphism replaces it by the
spectrum of the ideal-residue-field tensor algebra. Testing geometric
irreducibility over the algebraic closure gives a prime nilradical for the
double tensor product. Cancellation of the intermediate residue-field base
change identifies this with the tensor product in the algebraic prerequisite.
The generic point here is explicitly the prime nilradical; identifying an
arbitrary whole-space generic point with this prime is a separate reduction.

The final comparisons identify a whole-space generic point of an affine scheme
with the nilradical by taking vanishing ideals of its dense singleton. A scalar
avoids that point exactly when it is not nilpotent. Finally, universal
irreducibility of field tensor products whose field maps do not kill a scalar
implies geometric irreducibility of the actual restriction to its principal
open. A field point of that restriction gives the required ring map and scalar
nonvanishing. Pasting the restriction pullback square identifies any test
pullback with the corresponding affine field tensor product.

The generic-fibre tensor comparison is also provided for an arbitrary
whole-space generic point: its ideal equals the nilradical, so the point and
its actual fibre agree with those of the prime nilradical.

An affine morphism whose image misses the generic point is empty over some
principal neighbourhood of that point. If its ring-map kernel lay in the
generic prime, that prime would be minimal over the kernel, because the
nilradical lies in every prime. Mathlib's minimal-prime lifting theorem would
then put the generic point in the image. Consequently a kernel element avoids
the generic prime. Its principal open has empty preimage. This reduction does
not use finite type.
