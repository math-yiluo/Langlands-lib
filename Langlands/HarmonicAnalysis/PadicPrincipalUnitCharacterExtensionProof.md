# Proof of finite-order extension from actual principal units

This pair implements the theorem
`Langlands.HarmonicAnalysis.padicPrincipalUnitCharacterExtension.{u}` with exact
target `PadicPrincipalUnitCharacterExtensionStatement.{u}`. Worker 84 is the principal
author; Workers 394, 55 and 450 are coauthors for
the adapted implementations described below.

The openness helper adapts Worker 394's principal-unit openness implementation,
which is documented and reused in the public UnboundedConductorProof pair.
The principal-unit subgroup is open: its valuation-one condition is an open
valuation sphere, and its congruence condition is the inverse image of the open
integer ring under `a -> (a-1)/uniformizer^n`. This includes level zero.
The normalized-order continuity argument adapts Workers 55 and 450's
IntegralUnitCharacterExtensionProof to the supplied data. It uses the compatible
valuation's local constancy away from zero, followed by the exact ordered
value-group isomorphism, logarithm and negation.

Let K be the kernel of the monoid homomorphism taking a field unit to its
residue-normalized absolute value. The published theorem
isCompact_normalizedAbs_eq_one_units supplies compactness of K in the original
units topology. Each principal unit lies in K because its discrete valuation is
one and hence its normalized order is zero. Its inclusion f into K is injective,
continuous and open; openness follows by restricting the open principal-unit
subgroup embedding in the field-unit group to the subtype K.

The supplied valuative topology is identified with Mathlib's valuative topology,
so the field is nonarchimedean. The compatible additive uniform structure gives
Hausdorffness, and nonarchimedeanness gives total disconnectedness. Principal
units are locally compact because they form an open subgroup of the locally
compact field-unit group, and are totally disconnected by their continuous
injective inclusion in the field. Public Van Dantzig supplies their open-subgroup
identity basis. The public complex-character open-kernel theorem then makes
ker(eta) open. Its image N under f is an open subgroup of K.

Compactness gives a finite quotient K/N and a positive subgroup index m. The
index power theorem gives x^m in N uniformly. Injectivity of f identifies the
preimage of N with ker(eta). The public theorem
`Langlands.Topology.exists_character_of_open_finite_quotient` constructs a
continuous rho on K with rho^m=1 and rho composed with f equal to eta. Its
finite-group character-extension argument is imported rather than duplicated.

The map `P(a)=a*uniformizer^(-ord(a))` is a continuous monoid homomorphism on field
units. Its multiplicativity uses the actual nonzero-product order law, its
continuity uses the continuous discrete order map, and the uniformizer power law
gives ord(P(a))=0. Thus it induces the continuous homomorphism Q into K. For each
principal unit z the order is zero, so Q(z)=f(z); for the chosen uniformizer Q
has value one. Set chi=rho composed with Q. Evaluation of rho^m=1 proves
chi^m=1 with the same positive m. The two identities for Q give the required
restriction formula and uniformizer value.

This is an internal proof route using published Library results and pinned
Mathlib, with no new external-source theorem attribution. It covers zero level
and every prime, including two. Nontriviality, depth and norm/stabilizer
comparisons remain separate obligations.
