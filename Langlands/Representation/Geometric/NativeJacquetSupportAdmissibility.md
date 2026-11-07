# Actual universal native support filtration and conditional admissibility

This internal module specializes the published native support-image filtration
to the complete rational-norm coefficient algebra `RegularAlgebra r` and the
original full universal induced representation. The field/group universe `u`
and inducing-carrier universe `uV` are independent. The original positive source
half normalization and inverse output half normalization are retained.

The generic helper `nativeSmoothJacquetSupportGradedOrbitIsoAt` evaluates the
published native graded comparison at a smooth inducing representation. The
helper `nativeSmoothJacquetSupport_isAdmissibleAt` applies
`isAdmissible_of_objectRepFiltration` over a Noetherian coefficient ring to the
actual support images. The ambient full smooth induction is smooth, as are its
native quotient and its open-kernel character twist. Admissibility of the actual
grades therefore implies admissibility of that same normalized quotient. This
helper assumes grade admissibility only as an intermediate abstract lemma; the
universal specialization below derives it from the actual orbit geometry.

`universalNativeJacquetInducingInput` bundles the original universal inducing
action with its proved smoothness, using continuity of the original Levi
projection and smoothness of the complex inducing action.
`universalNativeJacquetSupportFiltration` evaluates the original finite native
support-image filtration at this input. Its ambient representation is the
original relation quotient of the full smooth induced representation, twisted
by the canonical inverse output half-modulus. It is a filtration of actual
invariant submodules from zero to the whole quotient, not a Grothendieck-group
identity or a replacement induced carrier.

`universalNativeJacquetOrbitPiece_eq` identifies the evaluated orbit piece with
compact induction of the original full orbit-stabilizer coefficient.
`universalNativeJacquetOrbitFunctorIso` identifies its native quotient and
normalization with `universalNativeOrbitJacquetRepresentation`.
`universalNativeJacquetSupportGradedOrbitIso` composes the generic evaluated
grade comparison with this identification. If the ordered representative is
`w`, the intersection datum uses `z = w⁻¹`; the proof uses the double-inverse
identity to obtain the same orbit representation. No normalization scalar is
cancelled or replaced.

`universalNativeJacquet_isAdmissible` proves admissibility over the complete
coefficient algebra of the original normalized native Jacquet quotient of the
full universal induced family. It assumes an admissible, actually supercuspidal
complex inducing representation. The original inducing projection is continuous.
The ambient rational-point group is locally compact, nonarchimedean, Hausdorff
and sigma compact, and the original source-parabolic left quotient is compact.
The geometric inputs are explicit:

- A finite `OrderedDoubleCosets` datum for the source and target point-image
  subgroups, with disjoint covering orbits and open initial unions.
- For each representative, an actual `GeometricLemmaIntersectionDatum` at its
  inverse, using the original source and target parabolics, Levis and radicals,
  and a simultaneous `DynamicRealization` of that datum.
- Compactness of the original output-Levi quotient `LeftQuotient K`, where `K`
  is the section preimage of that datum's `compactComparisonSaturation`.

The proof supplies the already proved Noetherianity of `RegularAlgebra r`.
For each actual grade it applies
`universalNativeOrbitJacquet_isAdmissible`, which derives orbit admissibility
from complex source admissibility and actual supercuspidality under these
geometric premises. It transfers admissibility through the inverse of the
graded orbit isomorphism, then applies the generic finite-filtration helper.
Thus the universal theorem assumes neither output admissibility, coefficient
fixed-module finiteness, nor a supplied finite-filtration conclusion.

The provenance is internal: this is an evaluation and assembly of the published
`CoefficientSupportJacquet`, `SingleSurvivingGrade`, `NativeOrbitNormalizedAdmissibility`
and smooth-admissibility extension APIs. It implements the finite-filtration
step needed for the coefficient-geometric-lemma route to Renard VI.9.2. Existence
of finite ordered orbit geometry adapted to actual intersection data and dynamic
realizations, and compactness of their original output quotients, remain proof
obligations. The unchanged global
`RationalSupercuspidalJacquetFamilyFiniteStatement` is not proved here.
