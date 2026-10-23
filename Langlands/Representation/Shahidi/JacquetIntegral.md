# Scalar Jacquet integrands and their stabilization domains

This derived prerequisite implements the scalar integrands in Shahidi,
*Fourier transforms of intertwining operators and Plancherel measures for
GL(n)* (1984), printed page 72, equation (0.2) and the swapped functional
below (0.3), together with the compact-open stabilization interpretation on
printed page 78, equation (1.1) and the paragraph following it. The registered
source is `shahidi-1984-fourier`, SHA256
`a10d5c605d94d4e85d0e5f453d6a8c233d91e3cb60d538f430d8ad900cbb6b29`.

The ambient functions here are actual functions on GL_(m+1+n+1)(F) with values
in an arbitrary algebraic complex vector space V. A supplied complex linear
functional ℓ on V extracts the scalar. The two positive block ranks are m+1
and n+1; field and carrier universes are independent. The construction does
not place a topology or norm on V. The integral layer assumes a topological
field in the sense of a field with an `IsTopologicalRing` topology, a measurable
structure on F, and the resulting product measurable structure on matrices.
No Borel compatibility or Haar hypothesis is required to define the relations.
The elementary integrand identities need only a field and topology for the
unitary additive character.

The source originally uses the tensor of the two actual Whittaker functionals
on the actual induced carrier. This unit separates the scalar integral
construction from that specialization: ℓ is an arbitrary actual linear
functional and f is an actual group function. It neither substitutes an
arbitrary predicate for an induced representation nor claims to construct
that representation. Restricting these formulas to the induced carriers and
supplying the tensor Whittaker functional remain a subsequent construction.

`jacquetIntegrand` is the complex-linear map sending f to the function

    a ↦ conjugate(χ(u′(a))) ℓ(f(w u′(a))).

Here a is an (n+1)-by-(m+1) matrix, u′ is the published actual exchanged
upper-radical embedding, w is the published all-positive block Weyl matrix,
and χ is the published standard Whittaker character. This is the scalar
product in (0.2), with its factors commuted in ℂ. The companion
`swappedJacquetIntegrand` sends f to

    a ↦ conjugate(χ(u(a))) ℓ(f(w⁻¹ u(a))),

where a has the opposite rectangular dimensions and u is the original upper
radical. Thus the two domains, Weyl choices and characters remain distinct
when the ranks differ. Linearity of both maps follows from linearity of ℓ
and distributivity of scalar multiplication.

`jacquetIntegrand_lower` uses the actual identity
`lower(a) = w u′(a) w⁻¹` to express the first integrand using the right
translate of f at `lower(a)`. More directly,
`jacquetIntegrand_rightTranslate_inv` proves that replacing f by
`g ↦ f(g w⁻¹)` changes its evaluation to `f(lower(a))`, precisely the
function translation preceding (1.1). The character stays the conjugate of
χ(u′(a)); because `w⁻¹ lower(a) w = u′(a)`, this is the coordinate form of
the source's χ′. These are pointwise algebraic identities. No unproved
measure change is used in their proofs.

`HasJacquetIntegral` and `HasSwappedJacquetIntegral` are Prop-valued relations
obtained by applying the published `HasStableIntegral` to those concrete
scalar integrands and the supplied actual measures on their respective
rectangular spaces. Each relation requires one compact open additive subgroup
K such that every compact open additive subgroup containing K has an
integrable truncation with the same scalar value. Their uniqueness lemmas use
the proved common-compact-open-upper-bound argument of `HasStableIntegral`.
This is eventual stabilization, not an assertion that the full noncompact
integrand is absolutely integrable.

Given existence of one compact open additive subgroup of the rectangular
space, `jacquetStableDomain` and `swappedJacquetStableDomain` are the actual
preimages of the scalar stable-integrability submodule under the integrand
maps. Their membership lemmas identify membership with existence of a
stabilized value. The hypothesis supplies the zero element and is not a
hypothesis that any particular nonzero function stabilizes.

`jacquetStableFunctional` and `swappedJacquetStableFunctional` restrict the
integrand maps to these domains and compose with the published linear stable
integral. Thus they are actual complex-linear functionals on precisely the
proved domains, choosing only the unique stabilized value. The
`hasJacquetIntegral_jacquetStableFunctional` and swapped lemmas verify the
relations for their values; the two `_eq` lemmas identify those values with
any supplied witness. Their proofs are the corresponding published scalar
stable-integral properties after restriction.

No theorem of stabilization for every induced section, Whittaker equivariance
or nonvanishing on induction, compatible Haar normalization, meromorphic
continuation, local-coefficient existence, or Theorem 5.1 is claimed here.
In particular these definitions do not assert that the stable domains contain
all smooth group functions. Those analytic and representation-theoretic
statements must be stated separately after the actual induced specialization.
