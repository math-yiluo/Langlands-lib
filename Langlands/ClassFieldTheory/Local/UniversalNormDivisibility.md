# Divisibility inside the actual universal norm subgroup

This derived support module makes the compactness step of universal-norm
divisibility explicit. Its conclusions remain conditional on arithmetic
universal-norm lifting and on downward directedness and closedness of the
actual finite abelian norm family. It does not construct these inputs or
prove the unconditional norm-separation or norm-existence targets.

`finiteAbelianNormFamily K` is the set of determinant-norm subgroups of all
actual finite abelian intermediate fields inside `AlgebraicClosure K`.
The existing `FiniteIntermediateExtension` packages each field with its
finite-dimensionality certificate without changing the field operations.
The bottom intermediate field makes this family nonempty. Membership in
the previously defined `universalNormSubgroup K` is equivalent to membership
in every member of this family.

`UniversalNormLifting` is a Prop-valued input, with every prime and every
pair of actual p-adic fields quantified in the same arbitrary carrier
universe. It asks that each universal norm of the base have a universal-norm
preimage under the actual determinant norm of the extension. No Galois
assumption is placed on that extension. Relative finite dimensionality is
derived from the given finite p-adic tower, rather than assumed separately.
This module does not assert that this input holds.

`universalNorm_prime_root_of_lifting` packages an actual finite intermediate
field as a p-adic field using its composed p-adic algebra and the compatible scalar-tower
certificate, applies the global lifting input, and supplies the result to `KummerNorm.prime_power_of_universal_lift`. Thus a universal norm
has a prime root in the ambient field-unit group, without a primitive-root
hypothesis on the base.

For `universalNorm_prime_root_mem_of_lifting`, fix one actual finite abelian
norm subgroup `N(E/K)`. Lift the base universal norm `a` to a universal norm
`b` of `E`. The preceding result writes `b = c^q` in `E`. The determinant
norm of `c` is a prime root of `a` lying in `N(E/K)`. This gives a root in
each norm subgroup separately. Apply the generic directed compact-fiber
intersection theorem from Worker 1769's `NormExistenceFiberSupport` to the
continuous power homomorphism. Its fiber is compact by
`isCompact_power_fiber`, since the prime exponent is nonzero. The supplied
downward directedness and closedness then give one root lying in every
finite abelian norm subgroup. The membership equivalence puts that root
inside the universal norm subgroup itself. The topology is exactly the one
stored in the supplied `TopologicalData`.

Two group-theoretic lemmas supply the remaining consequences. Induction by
multiplication with primes composes roots within any subgroup to obtain
roots of every positive natural order. In a commutative group, a subgroup
with all such roots lies in every finite-index subgroup `H`: choose a root
of order `H.index`, and use the fact that every element raised to this
index belongs to `H`. The final two theorems apply these lemmas to the
actual universal norm subgroup. The finite-index consequence does not
require openness.

The provenance is internal derivation from the preceding Kummer norm
support, the actual determinant norm homomorphism, the compact-fiber
theorems, and Mathlib's prime-factor induction and quotient-index power
identity. In particular, the arithmetic lifting and directed closed-family
properties remain explicit premises; neither they nor a class-field
correspondence is assumed to have been proved by compactness alone.
