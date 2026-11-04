# General standard intertwining integral on its actual domain

## Source and scope

The source is J.-L. Waldspurger, *La formule de Plancherel pour les groupes
p-adiques (d'après Harish-Chandra)*, IV.1, printed pp.277–278 (PDF pp.43–44),
DOI 10.1017/S1474748003000082. At the end of p.277 and the beginning of p.278,
the integral of `f(u' g)` over `(U ∩ U') \ U'` is defined by absolute
convergence against every smooth contragredient functional and existence of
a representing vector in the original inducing space. The source then
defines the standard intertwiner when these conditions hold for every
input and evaluation point. Its normalization is the positive Levi
half-modulus convention of I.3, printed p.243 (PDF p.9).

This module is an internal construction of that integral on the subspace
where its defining conditions actually hold. It combines the published
Levi-normalized induced-function model with smooth weak integration,
compact-open cofinality and compatible quotient measures. It does not
claim Theorem IV.1.1, which additionally proves convergence in a twist cone
and rational continuation. The output here is a function on `G` with
proved smoothness and, for a compatible measure, target-radical invariance.
Target Levi covariance and membership in target normalized induction
remain to be proved. No target parabolic or target semidirect decomposition
is an input to this unit.

## Objects and hypotheses

The ambient group `G` is locally compact and nonarchimedean. The actual
subgroups `P`, `M`, `U` have an `IsSemidirectDecomposition P M U`, and `U`
is closed. The inducing object `A` is the canonical complex `SmoothRep`
of `M`, with carrier universe independent of the group universe. The
source object is precisely
`DynamicNormalization.leviTwistedInductionFunctor h hU` applied to `A`:
first twist the Levi action by its positive Haar half-character, then
inflate and induce. Neither admissibility nor radical unimodularity is
needed for this construction.

`U'` is any subgroup of `G`. `QuotientSpace` is the actual left coset
space `LeftQuotient (U.subgroupOf U')`. Here `U.subgroupOf U'` consists
of those elements of `U'` lying in `U`, so its quotient is literally
`(U ∩ U') \ U'`. No normality, quotient group or chosen complementary
subgroup is introduced.

The domain constructions use an arbitrary measurable structure and
measure `ν` on this quotient. To select a unique linear operator, `M`
is additionally assumed closed. Closedness makes `M` locally compact,
and the inherited nonarchimedean structure supplies compact open
subgroups cofinal in its open subgroups. Smooth-dual separation then
gives uniqueness without a topology on the carrier of `A`.

For target-radical invariance, the additional inputs are measures `μU'`
on `U'` and `μI` on `U.subgroupOf U'`, right invariance of `μI`, Borel
structures on the intersection and quotient, and
`QuotientIntegration.IsCompatible (U.subgroupOf U') μU' μI ν`. The
invariance proof uses the right-translation measure-preserving field of
this compatibility relation. The relation also records nonzero
regularity and the Weil formula; it is a property of actual measures.

The final existence lemma assumes `G` is Hausdorff, `U'` is closed,
Borel structures are supplied on `U'`, the intersection and the quotient,
and `μU'`, `μI` are fixed regular two-sided Haar measures. It proves the
existence of a compatible quotient measure for these fixed inputs.
The absolute scale is therefore tied to the supplied subgroup measures.
Construction of the source manuscript's global system of Haar choices
and its reductive rational-point specialization is outside this unit.

## Descent and the domain

`source_unipotent_invariant` specializes positive Levi covariance at the
identity Levi element. Thus the actual source function satisfies
`f(u x) = f(x)` for `u ∈ U`.

`integrand h hU U' A g` is a linear map taking a source vector to the
quotient function represented by `u' ↦ f(u' g)`. It uses
`QuotientIntegration.descend` and the preceding invariance theorem;
`integrand_mk` records its exact value on representatives. Additivity and
homogeneity are verified on representatives. `integrand_right_action`
identifies the original induced right action by `t` with evaluation at
`g t`. `integrand_unipotent_mul` identifies evaluation at `u' g` with
right translation by `u'` on the left coset space. Both identities follow
from associativity and the actual function evaluations.

`HasIntegral f Jf` says, for every `g`, that every smooth functional `ℓ`
has an absolutely integrable scalar function `ℓ(f(u' g))` whose genuine
complex integral equals `ℓ(Jf(g))`. It is the published
`SmoothWeakIntegral.HasIntegral` relation applied to the descended
integrand.

`domain` is the intersection, over all `g`, of inverse images of the
published submodule of weakly integrable quotient functions. Its elements
therefore carry actual existence of a representing vector at every
evaluation point. `mem_domain` proves the equivalent formulation
`∃ Jf, HasIntegral f Jf` by pointwise choice. This definition does not
assert that all source vectors belong to the domain.

`HasIntegral.right_action` translates an existing representing function
by `g ↦ g t`. `domainSubrepresentation` consequently proves stability
of the domain under the original ambient representation. No convergence
is deduced from this algebraic stability alone.

## The selected integral and its properties

`compactCofinal` supplies the compact-open cofinality needed for uniqueness.
`operator` is a complex linear map from `domain` to `G → A`. At each `g`
it restricts `integrand` to the actual integrability submodule and applies
`SmoothWeakIntegral.integralLinear`. Choice occurs only within the
existence proof already carried by each domain element.

`operator_spec` proves that this selected function satisfies all original
smooth scalar tests. `operator_eq` identifies it with every other
representing function, using smooth-dual separation pointwise.
`operator_eval` expresses smooth-functional evaluation of the operator
as the genuine complex scalar integral on the quotient.

`operator_right_action` applies uniqueness to the translated representing
function. It proves commutation with the original source right action
on the stable domain. `operator_preserves_stabilizer` then shows that
every single open right subgroup stabilizing the entire input function
also stabilizes the entire output function. `operator_uniformly_smooth`
obtains such a subgroup from the smoothness of the actual source object.
The conclusion is uniform right invariance on all of `G`.

`operator_unipotent_mul` proves `Jf(u' g) = Jf(g)` for every `u' ∈ U'`.
The translated integrand has the same scalar integrals by the
measure-preserving right action on the quotient; composition preserves
scalar integrability. Uniqueness of the representing vector gives the
result.

Finally, `compatibleMeasure_exists` applies the published
`QuotientIntegration.compatibleMeasureExists` theorem to the closed
subgroup `U.subgroupOf U'` of the locally compact Hausdorff group `U'`.
Its closedness is the inverse image of the closed subgroup `U` under the
continuous inclusion of `U'` into `G`. This supplies the required measure
from the fixed two-sided Haar inputs without normality.
