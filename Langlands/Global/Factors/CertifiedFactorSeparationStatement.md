# Separation of actual certified pair factors

`CertifiedFactorSeparationStatement` is a derived conditional adapter from
common gamma factors to the existing arithmetic and automorphic L and
epsilon relations. It is a proposition definition; this file supplies no
proof.

The arithmetic inputs are actual local Weil–Deligne pair classes and a
representative of their tensor class. The two arithmetic polynomials are
the published determinant polynomials on the inertia invariants in the
monodromy kernel, for that representative and its actual dual, at the
geometric Frobenius. No new class-level Euler polynomial is defined.
The supplied common-closure reciprocity family, local-constant system,
system certificate and nontrivial additive character remain fixed.

The automorphic classes retain both positive ranks. Their gamma
certificate supplies actual smooth dual classes, certified original and
dual pair L-polynomials, and a certified coefficient/exponent pair for
epsilon through the existing Langlands-quotient relations. The field,
Weil carrier, automorphic carrier and epsilon-system carrier have
independent universe parameters, subject to the existing interfaces.

Both sides must satisfy their explicit no-common-root conditions under
reflection by `q⁻¹ X⁻¹`. `CertifiedAutomorphicPoleRegions` requires this
condition for every certified original/dual pair at every self-dual
measure. The arithmetic condition is imposed directly on the actual
tensor determinant polynomials. The adapter does not infer either
condition from gamma equality. Temperedness, essential unitarity,
supercuspidality and non-juxtaposition can supply sufficient conditions
through the separately owned GL and Weil pole-region branches; proving
those analytic inputs remains outside this adapter.

The common-gamma premise retains both existence of a self-dual measure
and existence of common certified gamma factors for every such measure.
The conclusion retains the same two measure quantifiers and identifies
both automorphic polynomials with the actual tensor and dual-tensor
polynomials. It identifies the corresponding rational reciprocal
L-factors and supplies the same coefficient/exponent pair as an
arithmetic and automorphic epsilon certificate for the given system.

The provenance is Henniart, *On the local Langlands conjecture for GL(n):
the cyclic case* (1986), §4.4, printed p.159, registered as
`henniart-1986-cyclic`. The generic algebraic input is the existing
`Langlands.Global.GammaSeparationStatement`; this adapter does not
replace or modify that target. Its conditional application to the
published actual factor interfaces is derived content. The spectral
variable is `X = q^(-s)`, reflection represents `s ↦ 1-s`, and epsilon
is the actual rational unit monomial.

Constructing common gamma factors from global functional equations,
highly ramified stability and almost-everywhere matching belongs to the
other H1 adapters. Actual local maps and fundamental classes enter
through those adapters, whose outputs can supply this premise without
changing their data. Global boundary nonvanishing remains an explicit
input in the pole/pairing branch, with its discharge assigned to the
parent common-library program. This target proves no unconditional
AssociatedFactorStatement, factor-existence theorem or correspondence.
