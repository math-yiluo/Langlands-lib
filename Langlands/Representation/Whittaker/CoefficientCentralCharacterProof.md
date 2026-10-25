# A central character on all coefficient images

Author: Worker 64.

The theorem `Langlands.Whittaker.coefficientCentralCharacter` proves the
published `Langlands.Whittaker.CoefficientCentralCharacterStatement` with
independent group and carrier universes. Its assumptions are exactly those of
the target: a smooth complex representation and a complex-linear equivalence
of its full equivariant-functional space with the complex field.

Choose the functional mapping to one under the supplied equivalence with the
complex field. Every equivariant functional is its scalar multiple. Precomposing
with a central representation operator preserves equivariance, so it acts on
the chosen functional by a scalar `c(z)`. Evaluating on one vector with nonzero
functional value proves that `c` preserves one and multiplication. Applying
this to inverses proves that the scalars are nonzero and thus define a
complex-unit-valued group character.

An open subgroup fixing the detecting vector gives, at each central `z`, the
open neighborhood of central `w` with `z⁻¹w` in that subgroup. The representation
operators at `z` and `w` agree on this vector, which forces equal character
values. This proves local constancy. The construction of neighborhoods follows
the published argument in `Smooth.Schur.Proof`, but the scalar here is derived
from the functional space rather than from irreducibility of the original
representation.

Every coefficient-image element has a vector preimage under `modelMap`.
The representation multiplication identity and the scalar law on functionals
therefore give the stated law on coefficient functions. Finally, evaluating
any competing character's law on the detecting vector's coefficient at the
identity proves uniqueness.

The source motivation and derived scope are those of the paired target:
JPSS (1983), printed page 393, uses central characters in the equal-rank
test-vector reduction. The result supplies that action on coefficient images
for possibly reducible representations. It does not prove the actual
unit-value test construction or the unconditional equal-rank analytic theorem.
