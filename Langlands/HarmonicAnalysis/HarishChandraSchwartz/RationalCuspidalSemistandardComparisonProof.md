# Cuspidal constant terms on the whole semistandard index

The theorem `rationalCuspidalSemistandardComparison` proves
`RationalCuspidalSemistandardComparisonStatement` from the module
`RationalCuspidalSemistandardComparison`, with every quantifier of that
statement: every nonarchimedean local field `F`, connected reductive
affine locally finite type `G`, maximal split torus `i`, generic
cocharacter `ν`, compact open subgroup `K` with `G(F) = P₀(F) K`, and
closed matrix representation `ρ` on a nonempty finite index. For every
`f` in `RationalSchwartzSpace hKc hPK ρ`, membership in
`rationalCuspidalSubmodule hKc hPK ρ` is equivalent to
`RationalSemistandardConstantTermsVanish f`. The proof uses only the
axioms `propext`, `Classical.choice` and `Quot.sound`.

## Standard convergence used in the proof

The private theorem `standardConstantTermConvergence` proves
`RationalSchwartzConstantTermConvergenceStatement` inside this module.
It is an auxiliary step of the comparison and is not exported.
`hasSpecialPacketCompact` supplies a special compact open subgroup `L`
with the standard point products, the simultaneous standard basis and
the Cartan covers of `G` and of each standard Levi. From the products
`L` gives `G(F) = P₀(F) L`. The theorem
`standardLeviIwasawaFactorsAt_of_factorization` then gives the Iwasawa
factorization of the standard Levi `M_J(F)` at `L`. The proved estimate
`rationalConstantTermEstimate` of Waldspurger II.4.5, printed
pp. 262–263, is applied through
`RationalConstantTermEstimateStatement.integrable_mul_mul`. That theorem
evaluates the estimate at `L`. It then uses
`rationalSchwartzSubmodule_eq`, independence of the Schwartz space from
the compact open Iwasawa subgroup, to reach the prescribed `K`. The
result is absolute integrability of `v ↦ f(x v y)` for every Haar
measure on each proper standard radical `U_J(F)` and all `x, y`.

## From the standard kernel to semistandard vanishing

Let `p` be a member of `SemistandardSpectralIndex i` with
`p.parabolic ≠ ⊤`. The private theorem `exists_standardRadical_comap`
finds a proper standard face and an inner conjugation carrying it to `p`:

1. `CocharacterPresentation.ofCoverage`, with the proved coverage
   theorem `semistandardSpectralDynamicCoverage`, gives a cocharacter of
   the torus. Its dynamic parabolic is `p.parabolic` and its dynamic
   unipotent radical is `p.radical`.
2. `exists_innerIso_comp_eq_dominant_cocharacter` conjugates that
   cocharacter by an inner automorphism `g ∈ G(F)` to a cocharacter `ξ`
   of the torus whose dynamic parabolic contains `P(ν)`. By
   `relativeRootSignInclusions`, this containment makes `ξ` pair
   nonnegatively with every simple relative root for `ν`.
3. The face `J = simpleRootFace i ν ξ` of simple roots orthogonal to
   `ξ` makes `ξ` a standard cocharacter for `J`
   (`isStandardCocharacter_simpleRootFace`). The comparison
   `standardCocharacter` identifies its dynamic parabolic and radical
   with `standardParabolic i ν J` and `standardUnipotent i ν J`.
   `Dynamic.parabolic_eq_comap_of_iso` and
   `Dynamic.unipotent_eq_comap_of_iso` transport these equalities through
   the inner isomorphism. Hence `p.parabolic` and `p.radical` are the
   pullbacks of the standard parabolic and radical along `innerIso g`.
4. If `J` were the full set of simple roots,
   `standardParabolic_simple_eq_top_of_relativeRootNegation` would give
   `p.parabolic = ⊤`. Hence `J = rootSet i ν I` is a proper face.

On rational points, `SubgroupFunctor.rationalPoints_comap_innerIso_hom`
identifies the radical points of `p` with the conjugate
`{x | g x g⁻¹ ∈ U_J(F)}`. Membership in the cuspidal submodule gives
`IsIntegrableUnipotentCuspidal` for every Haar measure on `U_J(F)`. The
private theorem `integrableCuspidal_of_comap_inner` transports this to
every Haar measure on the radical points of `p`. It uses the continuous
conjugation isomorphism `conjugationSubgroupContinuousMulEquiv` and
`isIntegrableUnipotentCuspidal_of_conjugation`, applied to the
conjugating element `g⁻¹`. That theorem pushes a Haar measure across the
isomorphism and replaces the translating arguments `x, y` by `x g⁻¹` and
`g y`. Finally
`isIntegrableUnipotentCuspidal_iff_semistandardConstantTermInd` extracts
the vanishing of `constantTermInd` with `semistandardUnipotentModulus p`
for every pair of group arguments.

## From semistandard vanishing to the standard kernel

`mem_rationalCuspidalSubmodule_iff_constantTermInd` reduces membership to
two conditions for each proper standard root subset `rootSet i ν I` and
each Haar measure on its radical: integrability of all two-sided
translates, and vanishing of the normalized constant term. The standard
triple `SemistandardSpectralIndex.ofStandard` is a member of the full
index. Its parabolic is proper by `standardParabolic_ne_top_of_ne_univ`,
using the relative root system from
`relativeRootSystemStatement_of_rootRankOneFactorizationStatement`.
Integrability is `standardConstantTermConvergence` above. Vanishing is
the hypothesis at this member, because
`semistandardUnipotentModulus_ofStandard` makes its modulus
definitionally `standardUnipotentModulus i ν J`.

## Sources

The source is Waldspurger (2003), registered as
`waldspurger-2003-plancherel`. The full semistandard indexing and Haar
conventions are those of I.1, printed pp. 238–240. The normalized
integral is that of III.6, printed p. 272. VIII.2.1, printed
pp. 321–322, uses the vanishing of these constant terms to characterize
cuspidal functions. The convergence estimate is II.4.5, printed
pp. 262–263. The Lean proof follows the conjugation argument above and
does not follow the source's recursive projection.
