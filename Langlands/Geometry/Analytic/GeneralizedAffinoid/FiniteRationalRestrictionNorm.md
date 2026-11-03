# Closed range and norm estimates for finite rational restrictions

This internal construction uses an actual presented affinoid algebra `A` over a
complete ultrametric normed field `K`, a finite type `I` with a chosen `Fintype`,
and a family `D : I → RationalChart K A` of positive-radius rational charts.
Every chart algebra is the existing closed weighted Tate quotient, with its
constructed quotient norm. The cover premise is that every point of the actual
Banach spectrum of `A` belongs to some chart locus. No nontriviality of the norm
on `K`, strictness, reducedness, or nonzero-quotient premise is imposed.

## Actual restriction and closed range

`finiteRestriction` is the continuous `K`-linear map from `A` to the finite
product of the actual chart algebras. Its component at `i` is exactly
`(D i).baseMap`. The structural-map identities for the existing intersection
restrictions prove `finiteRestriction_compatible` on the original overlap
quotients.

`range_finiteRestriction` uses the published
`wholeSpectrumRationalGluing` theorem to identify its range with all families
satisfying those pairwise overlap equations. The forward implication computes
both intersection restrictions on an element of `A`; the reverse implication is
the existence part of scalar gluing. `injective_finiteRestriction` applies gluing
uniqueness to two elements with equal restriction families.

`isClosed_range_finiteRestriction` expresses that equalizer as an intersection
of closed equality loci. Each equality compares two continuous functions obtained
by composing a product projection with the original bounded `K`-algebra map to
an intersection quotient. Thus closedness does not require any additional scalar
action on the intersection quotients. `norm_finiteRestriction_le` applies the
existing contractive bound for each rational structural map and the finite
product norm inequality.

## Auxiliary scalars and the lower bound

In namespace `AuxiliaryScalar`, let `L` be a nontrivially normed field, in an
independent universe, with a `NormedAlgebra L A` structure. No field embedding
from `K` to `L`, scalar tower, or completeness assumption on `L` is supplied.
`quotientNormedAlgebra` constructs the action on each chart quotient using the
ring homomorphism

`L → A → (D i).algebra`.

The norm estimate follows from submultiplicativity, contractivity of the rational
structural map, the normed scalar action on `A`, and the proved bound
`‖(1 : A)‖ ≤ 1`. This last bound retains the zero quotient.
`baseMapOver` is the original structural ring homomorphism with this induced
`L`-algebra compatibility. Its boundedness is unchanged.
`finiteRestrictionOver` bundles the same product restriction as an `L`-linear
continuous map. The induced instances are explicit in these definitions, so they
do not replace the existing `K`-algebra structures.

`exists_norm_bound` proves that there is a real number `C > 0` such that

`‖a‖ ≤ C * ‖fun i => (D i).baseMap a‖`

for every `a : A`. The original restriction map is injective and has closed range
by the preceding arguments. Both the domain and finite product target are
complete because they are actual affinoid quotients over complete `K`. Mathlib's
Banach closed-range theorem therefore gives an anti-Lipschitz constant over `L`.
Evaluating its distance bound at `a` and zero yields the norm estimate; increasing
the nonnegative constant by one makes it positive. Empty finite covers are
permitted: gluing still gives the injectivity needed by the same argument.

## Provenance and scope

This is a derived construction from the published actual rational chart,
intersection, scalar gluing and quotient Banach constructions, together with
Mathlib's continuous-linear closed-range form of the Banach open mapping theorem.
It makes no new assertion attributed to original literature. The norm estimate
requires the displayed auxiliary normed algebra action over a nontrivially normed
field. This module does not yet construct such an action for every original
algebra over a trivially valued field, nor does it construct finite-cover descent
of bounded algebra homomorphisms, arbitrary analytic atlas restrictions, analytic
etale sites, or equivariant sites.
