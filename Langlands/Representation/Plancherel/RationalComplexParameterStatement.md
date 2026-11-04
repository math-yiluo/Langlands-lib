# Periods and lifts of actual unramified complex characters

This is the exact algebraic parameter statement for the additive-image route
in Renard 2026 V.3.20. It is a proposition, with no proof in this file.
It uses the actual rational-character valuation image and the canonical
rational-point topology for every connected reductive group in the shared
nonarchimedean-local-field framework.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
V.3.19–V.3.20 is on printed pp.115–116/PDF pp.121–122; the exponential,
its period subgroup, basis-value lifting, real-part independence and
imaginary image are on printed p.116/PDF p.122. The actual image and norm
kernel come from V.2.3–V.2.6, printed pp.105–108/PDF pp.111–114.

## Exact target

Put `Lambda = Additive (rationalDiscreteValuationImage G)`,
`q = LocalField.residueCardinality F`, and `L = log q > 0`. The existing
construction has parameter space `Lambda →+ ℂ` and exponential
`E(lambda)(a) = exp (-lambda(a) * L)`.
Its period subgroup is the actual range
`(2*pi*i/L) Hom_Z(Lambda, ℤ)`, implemented by
`rationalImagePeriodEmbedding` and `rationalImagePeriodLattice`.

`RationalComplexParameterStatement` quantifies over every field `F` with
the displayed field, valuation, topology and nonarchimedean-local-field
instances, every group scheme `G` over `F`, and every proof that `G` is
connected reductive. It asserts all eight of the following.

1. Every complex character of the actual discrete image has a complex
   additive lift.
2. `E(lambda) = 1` if and only if `lambda` belongs to the stated period
   subgroup.
3. Two parameters give the same character if and only if their difference
   belongs to that subgroup.
4. For every character and every lift of it, the pointwise real part of
   that lift is the published normalized `rationalImageRealPart` of the
   character. Thus any two lifts have the same real part.
5. `E(lambda)` is unitary if and only if the real part of `lambda` is zero.
6. A character of the actual image is unitary if and only if it is
   `E(i * phi)` for some real additive functional `phi`, included in the
   complex parameter space by `rationalImageParameterOfReal`. The scalar
   action is pointwise multiplication by `Complex.I`; this is the source's
   image of `i a*` on the actual image space.
7. The canonical exponential onto actual continuous unramified characters
   of `G(F)` is surjective.
8. Two parameters give the same such actual-point character if and only if
   their difference belongs to the same period subgroup.

The last two assertions use
`rationalCanonicalUnramifiedComplexExponential`, whose formula at every
actual point is already part of the construction. The point group carries
`rationalPointTopology F G.X`. Affineness and smoothness, hence local finite
type, are derived from connected reductivity inside the statement; no
additional structural assertion or finiteness premise is assumed.
There is one independent universe parameter for the field and group
objects; the coefficient field is the actual `ℂ`.

## Normalization and retained obligations

The real part in clause 4 is `-log norm/L`, forced by `q^(-s)`. The raw
natural logarithm of the modulus is `-L` times this parameter. The source's
later raw-log notation is therefore not an equality with the real part of
an arbitrary lift under this exponential convention. The target retains
the explicit normalization of the construction.

The statement describes algebraic groups of additive functionals and
characters. It asserts no topology on the parameter space, continuity in
the parameter, discreteness or cocompactness of the period subgroup, or
homeomorphism from a quotient. Compactness of the existing unitary
character group does not by itself establish the source's stated
topological imaginary quotient.

The identifications with the algebraic character tensor space
`X*(G) ⊗ ℂ` and the split-center tensor spaces, the pure-tensor formula
using algebraic character norms, the algebraic torus structure, and the
compact quotient `i a*/(2*pi*i/L) Hom_Z(Lambda, ℤ)` remain separate
construction and proof obligations. This statement does not claim full
V.3.20 coverage.
