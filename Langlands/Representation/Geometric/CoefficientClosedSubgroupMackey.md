# Mackey support grades over an arbitrary coefficient ring

This internal construction generalizes the finite clopen-gluing argument of
`OrbitSectionExtensionProof` and the quotient assembly of
`ClosedSubgroupAssembly` from complex coefficients to an arbitrary commutative
ring `R`. It preserves the existing function carriers and orbit restriction
maps. The coefficient, group and inducing-carrier universes are independent.

The construction assumes a nonarchimedean locally compact Hausdorff
sigma-compact group, two closed subgroups, and an actual finite
`OrderedDoubleCosets` datum. Its representatives, orbit cover, disjointness and
open initial unions are geometric inputs. It supplies no such geometry for
rational parabolics and no normalized Jacquet comparison.

`coefficientClosedOrbitSectionExtension` extends every compact orbit section
with smooth inducing action to a compact ambient section supported in the
given open set, when the orbit is closed in that set. Local covariant sections
and quotient cutoffs already work over arbitrary commutative rings. The proof
uses the orbit homeomorphism to obtain agreement neighborhoods, compact clopen
patches covering the compact orbit support, and finite additive gluing. No
averaging, field division, dimension or finiteness assumption on the inducing
module is used.

`coefficientSupportStepOrbitRestriction_surjective` applies that extension
construction at an actual support step. The existing kernel theorem identifies
its kernel with the preceding support submodule.
`coefficientSupportGradedOrbitIso` applies the natural quotient first-isomorphism
construction. Its projection formula evaluates the class of a support section
at the actual orbit point `(representative i)⁻¹ * q`. The result is natural
under all `R`-linear inducing intertwiners.

This is a supporting construction for the coefficient geometric-lemma route
in Renard VI.9.2. It does not prove the task's native output-Jacquet finiteness:
actual rational orbit geometry, coefficient orbit-Jacquet identifications,
normalization balance, cuspidal vanishing, and fixed-module finiteness through
the resulting filtration remain separate obligations.

Author: Worker 1780.
