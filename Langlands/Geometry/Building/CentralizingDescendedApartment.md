# Centralizing a common apartment attached to a descended torus

The theorem
`KPApartmentData.exists_centralizing_conj_covering_of_descended_torus`
works over any field extension `K/k` in universe `u`. Let `G/k` be a group
scheme, and let `i:T → G` and `j:T′ → G` be homomorphisms of commutative
group schemes over `k` whose scalar extensions are maximal split tori of
the connected reductive group `G_K`. A split commutative group scheme
`A/K`, with a homomorphism `a:A → G_K`, factors through both of these
upstairs tori by `f` and `f′`.

Suppose `D` is apartment data for `i_K`, and a supplied transporter `g₀`
with torus isomorphism `e₀` takes `i_K` to `j_K`. Affineness of `G_K` and
monomorphism of `i_K` are explicit instances needed to form the supplied
quotient. No property of a local field or of a Galois-fixed point is
assumed. The theorem supplies `g ∈ centralizerPoints a` such that every
`g⁻¹σ(g)` normalizes `i_K`, for `σ ∈ Aut(K/k)`. For every point of the
same quotient, membership in the apartment translated by `g₀` is
equivalent to membership in the apartment translated by `g`.

This is a derived internal reduction, not a construction of a common
special apartment. In a proof of KP Proposition 9.3.11(1) in the supplied
quotient, the missing geometric input must still supply a descended
special torus `T′`, its inclusion and factorization of `a`, and one chart
containing the required points. The theorem only changes its transporter
while retaining the actual covered points.

The noncomputable definition
`KPApartmentData.centralizingConjCoveringOfDescendedTorus` chooses such a
representative from the proved existence theorem. Its value is a subtype
of the actual rational-point group, with the three specifications as its
certificate: centralizer membership, normalizer-valued coefficient
differences, and equivalence of chart membership for every point. The
underlying group element is its `.val`. The proved projection lemmas
`centralizingConjCoveringOfDescendedTorus_mem_centralizerPoints`,
`centralizingConjCoveringOfDescendedTorus_galoisDifference`, and
`centralizingConjCoveringOfDescendedTorus_covering_iff` expose these
certificates for use in a later construction. This choice uses
`Classical.choose` and `Classical.choose_spec`; it adds no geometric
existence assertion.

The implemented proof uses the published
`exists_centralizing_conj_of_isMaximalSplitTorus` from
`Langlands.GroupScheme.Reductive.TitsIndexCentralizerConjugacy` to
obtain a conjugator `g` and a torus isomorphism fixing `a`. The published
`mem_centralizerPoints` converts that last equation into membership in
the actual all-test centralizer evaluated at `Spec K`. The supporting
`inv_mul_rationalConjugate_mem_normalizerPoints_of_transporters` from
`Langlands.GroupScheme.Rational.TorusConjugatorGaloisCocycle` supplies the
Galois-difference condition because both embedded maximal tori descend
from `k`.

For chart membership in one direction, the published
`inv_mul_mem_normalizerPoints_of_transporters` gives the normalizer point
`n = g⁻¹g₀`. The original normalizer-equivariance theorem
`KPApartmentData.apartmentMap_smul` then gives
`g • D.apartmentMap (n • x) = g₀ • D.apartmentMap x`. The inverse
direction uses `n = g₀⁻¹g`. Thus no apartment comparison axiom or
assumed existence of a common apartment is introduced in this algebraic
step. All mathematical inputs other than the paired supporting cocycle
module are already published Library theorems.
