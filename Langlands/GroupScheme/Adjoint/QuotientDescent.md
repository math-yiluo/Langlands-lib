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

## Descent along fppf homomorphisms with full central kernel

Author: Worker 1366.

This derived construction supplies actual factorizations for a homomorphism
`q : G ⟶ A` of group schemes over an arbitrary scheme `S : Scheme.{u}`.
Assume that the underlying scheme morphism of `q` is flat, surjective and
locally of finite presentation, and that `kernelι q` is a scheme-theoretic
centre of `G`. The latter hypothesis says that the actual pullback kernel
has closed inclusion and its range is the full centre functor, tested on
every scheme over `S`.

In namespace `Langlands.GroupScheme.CenterQuotientDescent`, `schemeDesc`
constructs `A.X ⟶ Y` for every `Y : Over S` and every
`f : G.X ⟶ Y` invariant under right translation by the full centre.
`groupDesc` constructs `A ⟶ H` for every group scheme `H` over `S` and
every homomorphism `G ⟶ H` that kills the full centre.
`comp_schemeDesc`, `comp_groupDesc`, and their uniqueness lemmas give the
factorization equations and uniqueness. `schemeUniversalOfCenter` and `groupUniversal`
package these equations as unique-existence propositions. The targets and
test schemes range over the whole indicated categories in universe `u`.

The proof first identifies central points with points sent to the identity
using `kernelPointsEquiv`. Given any two scheme morphisms `a,b` with the
same composite with `q`, view them as points over their common base map.
Then `a⁻¹ * b` lies in the full centre, so invariance gives equality of
their composites with `f`. The effective epimorphism instance for flat,
surjective, locally finitely presented scheme morphisms in
`Mathlib.AlgebraicGeometry.Sites.Fpqc` supplies `EffectiveEpi.desc`.
Cancellation against `q` proves that the descended map is over `S` and
proves uniqueness. The product of `q` with itself is again flat,
surjective and locally of finite presentation. Cancellation against this
product proves preservation of multiplication; the unit equation follows
by composing with the unit of `G`. Thus the descended map is an actual
group-scheme homomorphism, including for noncommutative targets.

`Langlands.GroupScheme.IsAdjointQuotient.of_fppf` applies this construction
over a field. It requires connected reductivity of the source, adjointness
of the target, the three morphism properties and the actual full
kernel-centre identity. It then supplies both universal properties to
construct `IsAdjointQuotient q`. This helper does not prove that those
geometric hypotheses survive field extension.

The provenance is a categorical derivation from the existing actual-kernel
and centre interfaces and Mathlib's fppf subcanonicity theorem.
Conrad–Gabber–Prasad, *Pseudo-reductive Groups*, second edition (2015),
Definition A.1.11 and Example A.1.12, printed p.470 / PDF p.496, give the
source motivation: right-translation invariance characterizes the scheme
quotient, and flat surjective homomorphisms have this property by descent,
including with nonsmooth kernels. The general base scheme and arbitrary
targets here are proved from the imported effective epimorphism theorem;
they are not asserted to be the literal scope of that field-based passage.
No smoothness, reducedness or commutativity is assumed in this helper.

Source ID: `conrad-gabber-prasad-2015-pseudo-reductive`.
Retained source: `/home/taskhub/central-library/Conrad-Gabber-Prasad--Pseudo-reductive groups (book, 2nd edition)--2015.pdf`.
SHA-256: `1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.
The cited passage and Definitions A.1.8–A.1.10, printed pp.468–469,
were read directly; no source-specific errata note was present in the
public notes directories at preparation.

The original `CenterQuotientDescent.schemeUniversal` retains its weaker range-equality premise and original argument order. `schemeUniversalOfCenter` is the separately supplied full-centre interface.
