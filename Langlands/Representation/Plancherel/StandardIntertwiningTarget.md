# The target-normalized standard integral on its actual domain

This derived construction packages the actual smooth-dual standard
integral in the target positive Levi-normalized induction. It retains an
explicit squared intersection-modulus identity as a conditional premise.

The original source is Waldspurger (2003), I.3, printed p.243 (PDF p.9), and
IV.1, printed pp.277–278 (PDF pp.43–44). The former fixes positive
Levi-normalized covariance and uniform right smoothness; the latter defines
the integral by smooth contragredient scalar tests and an original-carrier
representing vector. This is an internal deduction from the existing
standard-integral construction and its explicit Levi law. It proves no
convergence cone, continuation or full-source convergence.

The actual subgroups have semidirect decompositions `P = M U` and
`P' = M U'` with the same actual Levi, with closed `U`, `U'`, and `M`.
The ambient group is locally compact, nonarchimedean and Hausdorff.
The group and representation-carrier universes are independent. Borel
structures on `U'`, `I = U.subgroupOf U'` and the actual nonnormal left
quotient `I \ U'` are supplied, with regular two-sided Haar measures
`muU'`, `muI` and an actual compatible quotient measure `nu`.

`SquaredModulusCompatibility` states the unresolved equality of actual
Haar moduli `deltaU(m) deltaU'(m) = deltaI(m)^2`. Its first two factors are
the existing closed restricted normalizer characters; the intersection
factor is the Haar modulus of the actual restricted conjugation
automorphism of `I`. It is not assumed to follow from arbitrary semidirect
data, and is not asserted as proved for reductive rational points here.

The scalar lemma takes the positive square root of this equality and gives
`sqrt(deltaU) * deltaU'/deltaI = sqrt(deltaU')`. The existing Borel-instance
comparison identifies the target closed character with the numerator of
the actual quotient-conjugation factor. Thus `leviFactor_eq_targetHalf`
identifies the previously proved explicit factor with the positive target
half-character.

`operator_target_covariant` combines that identity with the actual Levi
law and target radical invariance. `targetOperator` uses the existing
uniform right-smoothness result to construct a target induced function;
its linearity follows from the original integral's linearity.
`targetOperator_eval` identifies every value with that integral.
`targetOperator_spec` retains its original convergence and representing
vector specification. Finally `targetIntertwiner` uses the proved
right-translation identity to establish equivariance for the ambient group.

The domain is precisely the existing scalar-convergence and
representability subrepresentation. No analytic convergence conclusion is
inserted as an additional domain-membership premise or claimed for all
source vectors. The shared reductive squared-modulus proof, its ambient
intersection/conjugation comparison, general convergence, rational
continuation, composition scalars and Plancherel remain open obligations.

For precision, the scalar lemma needs only nonnegative real `a`, `b`, `c`,
`c != 0` and `a * b = c^2`. The compatibility predicate and
`leviFactor_eq_targetHalf` need the ambient locally compact nonarchimedean
group, both actual semidirect decompositions, closed radicals and the
displayed Borel structures on `U'` and `I`; they do not need a chosen
measure on the quotient, a representation, closed `M` or Hausdorff `G`.
The proof gives `U'` and `I` the local compactness instances induced by
their closed inclusions. In the character comparison, the published
`SiegelSetMeasure.mulEquivHaarChar_congr` compares the canonical Borel
structure used by `closedRestrictCharacter` with the supplied Borel
structure. Thus no equality of those measurable-space instances is
assumed as extra data.

The remaining declarations use all the measure, representation,
closed-Levi and Hausdorff hypotheses stated above. Neither admissibility
nor irreducibility of the inducing representation is used. No topology
or norm on its original carrier is required. The two regular Haar
measures are fixed actual measures, and compatibility concerns the
actual supplied quotient measure. The construction never changes that
measure to obtain covariance.

The scalar proof first derives
`sqrt(a) * sqrt(b) = c` using multiplicativity of the nonnegative square
root and `sqrt(c^2) = c`. Multiplying the desired division identity by
the nonzero `c` reduces it to commutative multiplication, using
`sqrt(b) * sqrt(b) = b`. Positivity of the actual intersection Haar
modulus supplies the required nonzero denominator. Coercion of this
identity to the complex scalars gives `leviFactor_eq_targetHalf`.

For `operator_target_covariant`, associativity first writes
`m * u' * g` as `m * (u' * g)`. The previously proved Levi law acts on
the latter argument, radical invariance removes `u'`, and the scalar
comparison gives exactly the target positive half-character. The
existing `leviNormalizedFunctionOf` then combines this full covariance
with a uniform open right stabilizer of the output to produce an
actual smooth induced vector. Choice is used only to select that
already proved stabilizer; equality of induced vectors is determined
by the underlying functions.

`targetIntertwiner` has type `Representation.IntertwiningMap` from
`domainSubrepresentation.toRepresentation` to the representation
underlying the existing target
`DynamicNormalization.leviTwistedInductionFunctor`. Its linear map is
literally `targetOperator`. Extensionality through the two induced
function subtypes reduces ambient equivariance to the previously
proved `operator_right_action`, whose action is right translation
`f(g) -> f(g * t)`. Thus this is a target-valued map with the original
scalar-integral specification, not merely a covariance assertion
about an unrelated function.

Waldspurger IV.1 defines a map on the entire induced space when its
convergence and representability conditions hold for every `f,g`;
IV.1.1 then proves convergence in a character cone and rationality for
finite-length inducing representations. This module proves neither
of those assertions. Its conditional target map has exactly the
existing actual domain, and the squared-modulus premise remains an
unproved geometric input here. It is not an authorized external
structural assumption for completion of the Plancherel program; its
proof and actual reductive comparison must still be supplied.
