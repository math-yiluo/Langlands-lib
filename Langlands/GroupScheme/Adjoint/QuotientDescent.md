# Descent through a quotient with the full centre as kernel

Author: Worker 1350.

This internal derived unit proves the arbitrary-target universal properties
needed in the adjoint quotient interface. It constructs no quotient and does
not prove `AdjointQuotientExistenceStatement`.

For an arbitrary base scheme `S` in universe `u`, let `q : G → A` be an actual
group-scheme homomorphism whose actual kernel range equals `center G`. The
centre is the published all-test functor, including restriction along every
further test morphism. Assume the underlying scheme map of `q` is flat,
surjective and locally of finite presentation. Then every actual scheme map
`f : G.X → Y` over `S` that is invariant under right translations by central
points factors uniquely through `q`. The target `Y` is any scheme over `S`
in the same universe, with no affineness, separatedness or finiteness premise.
No pointwise surjectivity of `G(T) → A(T)` is assumed.

The implementation uses the actual kernel points equivalence to see that
`x⁻¹y` is central whenever `q(x) = q(y)`. Centre invariance gives
`f(x) = f(y)`. Given two maps of underlying schemes with equal quotient
images, their structure maps to `S` agree, so they can be regarded as points
on one common object of `Over S`. This supplies the equalizing condition for
Mathlib's `EffectiveEpi.desc`. Its effective epimorphism instance follows
from flatness, surjectivity and local finite presentation. Cancellation
establishes compatibility with the structure map to `S` and uniqueness.
`schemeHom`, `overHom` and their factorization theorems retain the actual
scheme and slice morphisms.

For a field `k : Type u`, `isAdjointQuotient_of_fppf` assembles the full
published `IsAdjointQuotient q` from connected reductivity of `G`, adjointness
of `A`, the three fppf conditions, and
`IsSchemeTheoreticCenter (kernelι q)`. Its scheme universal property is the
preceding descent theorem. For its group universal property, killing the
centre implies `kernelι q ≫ f = 0`. Both groups have affine underlying
schemes, so `q` is quasi-compact. The published `FpqcHomDescent.hom`, `fac`
and `unique` then give the unique group-scheme homomorphism to any group
scheme over `Spec k`, without any finiteness or affineness assumption on
that target. This reuses the existing proof of the group laws rather than
assuming them for the descended morphism.

All mathematical inputs are the published centre and kernel APIs, the
published `Langlands.GroupScheme.HomDescent` construction and pinned
Mathlib's proved effective epimorphism and affine morphism results. These
are intrinsic category-theoretic consequences of the supplied morphism.
There is no external source assertion introduced as an unproved premise.
In particular, nonsmooth centres and positive characteristic remain in
scope, and no finite-kernel condition is added. Existence of the morphism
and adjointness of its target remain separate obligations.
