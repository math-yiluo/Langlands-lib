# Naturality of the actual normalized compact comparison

This internal deduction constructs the original maps on the normalized compact
source, the ordinary Jacquet coefficient and its compact-induced target. It
proves that the existing actual normalized compact comparison commutes with
these maps. The original positive inducing half, negative target half and full
intersection coefficient character remain in all actions. The full rational
geometric exact-K0 expansion remains open.

Use the original groups and notation of
`RationalGeometricNormalizedCompactFormula`: Q = P_I, L = M_I, H is the literal
subgroupOf copy of P_I intersect n P_J n⁻¹ in Q, and K is the literal subgroupOf
copy of M_I intersect n P_J n⁻¹ in L. The source radical S and common Levi Ls
are the subgroupOf copies of M_J intersect n⁻¹ U_I n and M_J intersect n⁻¹ M_I n
inside M_J. The maps f, p and s are respectively the original conjugate
coefficient projection, its restriction to the target Levi intersection and the
inclusion of M_I in P_I. Chi is the original positive half-character of U_J,
kappa the original inverse half-character of U_I, and eta is exactly
`geometricNormalizedCompactCharacter` on all of K.

`geometricNormalizedCompactSourceMap` first twists an original coefficient
intertwiner a by chi, restricts it along f and applies `compactInducedMap H`.
It then descends along the actual kernel of the original Levi projection dI,
restricts along s and twists by kappa. The representative law
`geometricNormalizedCompactSourceMap_mk` states that the class of F maps to
the class of the original compact function with pointwise values a(F(q)).

`geometricNormalizedCompactCoefficientMap` is the original ordinary Jacquet map
`Jacquet.map S Ls hSource.levi_le_normalizer a`, restricted along p and twisted
by the unchanged eta. Its representative law sends the ordinary class of v to
the ordinary class of a(v). `geometricNormalizedCompactTargetMap` applies
compact induction from K to this coefficient map. Its evaluation law gives
exactly the ordinary Jacquet map applied to each original function value.
These definitions and representative laws require no assumed comparison or
character-balance identity.

`geometricNormalizedCompactIntegrand_natural` proves equality of the actual
quotient simple functions: the integrand of the pointwise-mapped compact
function equals the original integrand mapped by the ordinary Jacquet linear
map. The proof uses extensionality and induction on an actual quotient
representative q. The two original-function representative formulas from
`RationalGeometricNormalizedCompactFormula` and `Jacquet.map_mk` reduce the
claim to the same class of a(F(q s(l))). This identity uses the quotient's
Borel measurable structure and does not require ambient Hausdorffness.

For `geometricNormalizedCompactEquiv_eval_natural`, the measures are exactly the
original Borel kernel Haar measure, intersection Haar measure and selected
compatible quotient measure. As in the formula module, right invariance and
compatibility imply that this quotient measure is finite on compact sets.
The proof evaluates both comparisons using
`geometricNormalizedCompactEquiv_eval_mk`. It substitutes the integrand
naturality identity and applies `AlgebraicIntegral.integral_linearMap` with the
existing finite measurable support theorem. Complex linearity commutes the
ordinary Jacquet map with the exterior kappa(l) factor. Thus the value after
mapping the original compact function equals the ordinary Jacquet map of the
original comparison value, at every l in M_I.

`geometricNormalizedCompactEquiv_natural` is the resulting equality of the two
actual compact functions, for every vector in the original normalized compact
source. The proof uses induction on the original target-radical coinvariant
class, extensionality of compact functions and the preceding evaluation-level
identity. There is no change of source carrier or compact comparison map.

The field universe u and the source and target coefficient universes uV/uW are
independent. No finite-dimensionality, finite-length, characteristic-zero,
splitness, positive-rank or choice of minimal Weyl representative is introduced.
The declarations retain the original rational-point topology, local compactness,
nonarchimedean structure, closed original subgroups, continuous original Levi
projections, compact-limit property of U_I and source/target decomposition
proofs at their respective scopes. Ambient Hausdorffness is used for the
canonical quotient-measure and whole-comparison results. The original standard
cocharacter and point-normalizer comparison hypotheses are retained from the
named actual comparison.

This is an internal consequence of the published map, coinvariant and actual
compact-comparison APIs and the original-function integral formulas. Its proof
bodies add no geometric expansion, adjointness, cuspidal-support, character
independence or classification premise. The imported closure is larger.
Whole-common-Levi distinct-radical balance, identification with the normalized
geometric-term coefficient, compact/full induction, ordered filtration and the
final exact-K0 equality remain separate obligations. A categorical natural
isomorphism is not bundled in this module.
