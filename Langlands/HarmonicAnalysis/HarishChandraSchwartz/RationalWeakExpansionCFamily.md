# The c-family `c_{P'|P}(s, ω)` and the weighted family `c̃_{P'|P}(s, ω)`

Author: Worker 131, task `b2eba110-082e-4b07-9076-f64b90cd0dc3` (Task 7454, revision 1), item 4.

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeakExpansionCFamily`,
namespace `Langlands.HarishChandraSchwartz.WeakExpansion`.

## Purpose

Waldspurger V.1 (printed pp.288–289) defines, for `s ∈ W(M'|G|M)`,

> `c_{P'|P}(s, ω)(v ⊗ v̌) = γ(G|M')⁻¹ [J_{P_s|s·P}(sω)λ(s)v ⊗ J_{P̃_s|s·P}(sω̌)λ(s)v̌]`,
> `P_s = (M' ∩ s·P)U'`, `P̃_s = (M' ∩ s·P)Ū'`,

and identifies the result with an element of `I^{G×G}_{P'×P̄'} L^{M'}(sω, M' ∩ s·P)`. Corollary
V.2.3 (printed p.294) concerns `ω ↦ µ^G(ω) µ^{M'}(sω)⁻¹ c_{P'|P}(s, ω)`. This module defines both
families on the actual groups, by convergent integrals only, with the published intertwining and
measure constructions. Rationality and regularity are targets (module
`RationalWeakExpansionTargets`), not premises.

## Data and conventions

- `F` is any nonarchimedean local field (any characteristic, universe `u`). The representation
  carrier universe `uV` is independent of `u`. `G` is connected reductive (`hG`), not necessarily
  split or quasisplit. `i : T ⟶ G` is a maximal split torus (`hi`) and `ν` a generic cocharacter
  (`hν`).
- `I, I'` are finite sets of simple roots. `M = M_I(F)` is the literal subgroup
  `standardLeviPoints i ν (rootSet I)` of `G(F)`, written `𝐌`, and `P = P_I(F)`.
  `M' = Standard.leviScheme i ν (rootSet I')` is the actual Levi scheme (`lowerAmbient`).
- `ζ` is a standard cocharacter of `I` (`hζ`) and `ζ'` one of `I'` (`hζ'`). They only name the
  parabolics: the dynamic parabolic of `ζ' ∘ i` is `P' = P_{I'}(F)` and that of `(-ζ') ∘ i` is
  `P̄'`.
- `n : normalizerPoints i` with `hn : n M_I n⁻¹ ⊂ M'` represents `s`. Later modules take `n` from
  the published representative system `Representatives` of `RationalWeakExpansionWeyl`.
- `K` is a compact open subgroup of `G(F)` (`hK`). It normalizes the Haar measures of all
  intertwining integrals and the constant `γ(G|M')`, as in the source (I.1 and IV.1, one fixed
  `K`). `hPK` is the Iwasawa decomposition `G(F) = P_∅(F) K`. On `M'`, a compact open subgroup
  `K'` with an Iwasawa decomposition for `M' ∩ s·P` (`hPK'`) is used for the fixed compact
  pictures. `K'` only chooses coordinates for the lower coefficient space. The targets module
  takes `K'` to be the compact subgroup of the lower density package, which under
  `CommonCompactNormalization` is `K ∩ M'(F)` read on the Levi scheme; this is the literal compact
  picture `I^{K∩M'×K∩M'}_{K∩M'∩s·P×K∩M'∩s·P}` of printed p.294.
- `hCST : CentralSplitTorusCharacterStatement` is used, through Worker 614's published lemma `squaredModulus_of_centralSplitTorusCharacter`, to discharge the squared-modulus premise
  of the standard integrals. It is one of the hypotheses that `µ^G` already takes.

## Groups

The three relevant cocharacters of `T`, composed with `i`, are

- `θ_s = (n·ζ) ∘ i`, with dynamic parabolic `s·P = n P_I(F) n⁻¹` and Levi `s·M`
  (`conjugatedCocharacter_dynamic` of `RationalWeakExpansionLowerGeometry`);
- `ψ_α = auxiliaryCocharacter i α (n·ζ) ∘ i` for `α = ζ'` and `α = -ζ'`. For `α = ζ'` this is
  `cParabolicCocharacter` and its parabolic is `P_s = (M' ∩ s·P)U'`; for `α = -ζ'` it is
  `cOppositeParabolicCocharacter` and gives `P̃_s = (M' ∩ s·P)Ū'` (module
  `RationalWeakExpansionAuxiliaryParabolics`, Worker 614).

Proved here:

- `mem_conjugatedParabolic_iff`, `mem_conjugatedRadical_iff`,
  `mem_conjugatedLevi_iff_of_centralizer_eq`: `x ∈ s·P ↔ n⁻¹ x n ∈ P_I(F)`, and the same for the
  radical and the Levi (from `conjugatedCocharacter_dynamic`, `conjugatedLevi_points` and
  `SubgroupFunctor.rationalPoints_comap_innerIso_inv`).
- `outer_isRepresentedBy`: for `α` with `Z_G(α ∘ i) = M'`, the centralizer is represented by
  `Standard.leviHom`. `outerCentralizer_pos` and `outerCentralizer_neg` give this for `±ζ'`.
- `centralizer_auxiliary`: `Z_G(ψ_α) = Z_G(θ_s) = s·M` (`auxiliaryParabolic_geometry`).
- `auxiliary_realization`: `P(ψ_α)` and `U(ψ_α)` are the extensions from `M'` of the parabolic
  and radical of the lower cocharacter `χ_s`, and `Z(ψ_α)` is the image of `Z_{M'}(χ_s)`. The
  last identity uses the published `SubgroupFunctor.map_comap` and `hn`. These are exactly the
  hypotheses of the published `RealizedLeviStages`.

## One factor

For `α` as above and a representation `B` of `M_I(F)`, `cFactor B hB` is the composite

1. `factorTranslation`: `λ(s)`, `f ↦ f(n⁻¹ ·)`, from `I^G_{P_I} B` to the induction from `s·P`
   of the conjugate `ⁿB = B(n⁻¹ · n)` on `s·M`. This is the published
   `inductionConjugationIsoApp`.
2. The published `normalizedInductionLeviEquiv` (same functions, Levi-twisted form).
3. `factorIntertwiner`: `J_{P_α|s·P}`, the published `StandardIntertwining.fullSourceIntertwiner`
   between the two parabolics with common Levi `s·M`. Its measures are the published pair
   measures `pairQuotientMeasure K hK θ_s ψ_α`, `radicalHaar ψ_α K hK` and
   `pairIntersectionHaar K hK θ_s ψ_α`, normalized at `K` as in the source. At the twist of a
   representation by an unramified parameter it is the published `pairFamily`. Its hypothesis
   `hB : FactorConverges … (ⁿB)` is the full convergence domain of that integral: every vector
   has absolutely convergent smooth-dual integrals, represented in the carrier. This is a domain
   condition, not an analytic premise.
4. `factorRestriction`: the value at `1` of the published induction-in-stages comparison
   `RealizedLeviStages.inductionInStagesIso` through the actual Levi scheme `M'`. On functions it
   is `f ↦ (m' ↦ δ_{P(α)}(m')^{-1/2} f(m'))` (`inductionInStagesIso_hom_eval`), where `P(α)` is
   `P'` for `α = ζ'` and `P̄'` for `α = -ζ'`. This is Waldspurger's map `v ↦ v_s`, resp.
   `v̌ ↦ v̌_s`, in the proof of V.1.1 (printed p.289):
   `v_s(m') = δ_{P'}(m')^{-1/2} (J_{P_s|s·P}(sω)λ(s)v)(m')`,
   `v̌_s(m') = δ_{P̄'}(m')^{-1/2} (J_{P̃_s|s·P}(sω̌)λ(s)v̌)(m')`.
5. `restrictedConjugateEquiv` and the published `normalizedInductionEquivOfEquiv`: the
   coefficient of the restricted function acts by `B(n⁻¹ j(m') n) = B(e⁻¹ m')`, so the identity
   of the carrier is an equivalence with `sB = B ∘ e⁻¹` (`e = lowerLeviConjugation`).

So `cFactor B hB : I^G_{P_I} B → I^{M'}_{M'∩s·P}(B ∘ e⁻¹)`. `evalOneLinear` is evaluation at `1`
as a linear map.

## The c-family

- `CConverges B`: joint convergence: `J_{P_s|s·P}` converges on `ⁿB` and `J_{P̃_s|s·P}`
  converges on `ⁿB̌`. In the source these are the points where both integrals defining
  `c_{P'|P}(s, ω)` are defined.
- `cDualFactor`: the factor for `α = -ζ'` applied to `B̌`, followed by the published
  `contragredientPullbackIso`, so that it lands in `I^{M'}((B ∘ e⁻¹)ˇ)`.
- `cMap B hB : L(B, P) → L^{M'}(sB, M' ∩ s·P)` (Lean `productInducedCoefficientObject`) is
  `γ(G|M')⁻¹ • T_{M'} ∘ (cFactor ⊗ cDualFactor) ∘ T_G⁻¹`. Here `T` is the published
  `normalizedProductInductionTensorEquiv`. Its compactness hypotheses are discharged from the
  Iwasawa decompositions by the published `compactSpace_leftQuotient_of_compact_representatives`.
  `γ(G|M')` is the published source gamma `RationalDynamicSource.gammaReal (ζ' ∘ i) K hK` of the
  outer parabolic `P'` at `K`. On `v ⊗ v̌` the value is `γ(G|M')⁻¹ (v_s ⊗ v̌_s)`. This is the value
  at `(1, 1)` of the source's element of `I^{G×G}_{P'×P̄'} L^{M'}(sω, M' ∩ s·P)`. The targets
  only use this value: `E^{P'}_{M'∩s·P}` followed by evaluation at `(1, 1)` is
  `E^{M'}_{M'∩s·P}` of it (printed p.304).
- `cDomain A`: the parameters `z ∈ X(M_I)` with `CConverges (A ⊗ z)`. No openness or nonemptiness
  is asserted.
- `twistPullbackEquiv`: `s(A ⊗ z) = sA ⊗ sz`, with the identity on the carrier.
  `sz = lowerUnramifiedCharacterConjugation z` (module `RationalWeakExpansionLowerOrbit`).
- `cFamily A z : L(A ⊗ z, P) → L^{M'}(sA ⊗ sz, M' ∩ s·P)` for `z ∈ cDomain A`.
- `cCompactFamily A z`: the same map read in the fixed compact pictures, through the published
  `productInducedCompactEquiv` on both sides. This is the form of Waldspurger IV.1 and of the
  proof of V.2.3, where `L(ω ⊗ χ_λ, P)` is identified with `I^{K×K}_{K∩P×K∩P}(E ⊗ Ě)`. Rationality
  in `z` is expressed in this form.

## The weighted family

- `rationalValueAt f hz`: the value `m(z)/n(z)` of a rational function at a complex point where it
  is regular. `rationalValueAt_eq` (proved) shows independence of the presentation.
- `packageDensity P`: the published `RationalPlancherelDensity.plancherelDensity` with the data of
  a density package. Its unitary values are the package weight.
- `standardLeviUnramifiedRestrict`: `z ↦ z ∘ e`, `X(M_I) → X(Z_G(ζ ∘ i))`, the complex version of
  the published `standardLeviCharacterRestrict`. `µ^G` is evaluated at this point.
- `cWeightedDomain`: `z ∈ cDomain π` such that `µ^G` is regular at `π ⊗ z`, `µ^{M'}` is regular
  at `s(π ⊗ z)`, and the value of `µ^{M'}` there is **nonzero**. Here `µ^G` is the density of a
  `DensityPackage` for `π ∘ e` on `Z_G(ζ ∘ i)(F)` (the data of the published
  `standardLeviPlancherelWeight`), and `µ^{M'}` the density of a `LowerDensityPackage`. For
  `µ^{M'}` the parameter is `(parameterTransport χ_s)⁻¹(sz)`. Regularity of a rational function
  at a point only provides a presentation with nonvanishing denominator; it does not exclude a zero
  of the function. The nonvanishing condition is therefore stated separately.
- `CommonCompactNormalization` (structure, a `Prop`): the common source normalization of the
  Haar measures. Its fields are `PG.K = K` (the density `µ^G` is formed with the compact `K` of
  the c-map) and `PM.K = leviSchemeCompact K` (the lower density `µ^{M'}` is formed with
  `K ∩ M'(F)`, read on the actual Levi scheme by the published `leviSchemeCompact`). The
  continuations, convergence and irreducibility domains and regularity witnesses of the two
  packages stay independent. Without it the densities could be formed with measures normalized by
  unrelated compact subgroups, and the weighted map would differ from the source's by a constant.
  For example, for `G = GL₂`, `M = M' = T`, `n = 1`, replacing `PG.K = K₀ = GL₂(O_F)` by the
  conjugate `K₁ = u(ϖ⁻¹) K₀ u(ϖ⁻¹)⁻¹` multiplies the lower-root Haar measure, `γ` and `j` by `q²`,
  hence `µ^G = γ²/j` by `q²`.
- `cWeightedCompactFamily hN z = µ^G(π ⊗ z) µ^{M'}(s(π ⊗ z))⁻¹ • cCompactFamily π z`, defined
  only under `hN : CommonCompactNormalization`. The hypothesis restricts the inputs; it does not
  enter the formula. Since the value
  of `µ^{M'}` is nonzero on the domain, the inverse is an actual inverse, and the scalar is the
  value at `z` of the rational function `µ^G(ω) µ^{M'}(sω)⁻¹`. So the map is `c̃_{P'|P}(s, π ⊗ z)`
  of V.2.3 at points where it is given by convergent integrals.
- Points where `µ^{M'}(s(π ⊗ z)) = 0` are excluded on purpose. In the proof of V.2.3 (printed
  p.294) the quotient `µ^G(ω) µ^{M'}(sω)⁻¹` is a rational function in which the common
  reduced-root factors cancel before specialization. At a common zero of the two densities the
  quotient can be regular and nonzero although both specialized values vanish (for instance
  `G = GL₂ × GL₂`, `M` the diagonal torus, `M' = GL₂ × T₂`, `s = 1`, at `t₁ = 1`, `t₂ = q²`).
  A definition by specialized values would give `0` there. At such points `c̃` is given only by
  the rational continuation of the targets module (`WeightedCExtension` in
  `RationalWeakExpansionTargets`), which agrees with `cWeightedCompactFamily` on the interior of
  `cWeightedDomain`.

## Comparison with the source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après Harish-Chandra*,
J. Inst. Math. Jussieu 2 (2003), 235–333 (literature id `waldspurger-2003-plancherel`).

- V.1, printed p.288: "`c_{P'|P}(s, ω) : L(ω, P) → I^{G×G}_{P'×P̄'} L^{M'}(sω, M'∩ s·P)`", with
  "`P_s = (M'∩ s·P)U'`, `P̃_s = (M'∩ s·P)Ū'`". Printed p.289: "`c_{P'|P}(s, ω)(v × v̌) =
  γ(G|M')⁻¹[J_{P_s|s·P}(sω)λ(s)v ⊗ J_{P̃_s|s·P}(sω̌)λ(s)v̌]`. Rappelons que `λ(s)` est la
  translation à gauche par `s`." The four ingredients are, in order, `factorTranslation`,
  `factorIntertwiner`, the tensor product and the factor `γ(G|M')⁻¹`.
- The source then says "L'opérateur `c_{P'|P}(s, ω)` est rationnel en `ω`". Rationality is not
  asserted here. `cFamily` is defined only where both integrals converge, and the regularity of the
  weighted family is the target `WeightedCRegularityStatement`.
- Proof of V.1.1, printed p.289: the maps `v ↦ v_s`, `v̌ ↦ v̌_s` with the factors `δ_{P'}^{-1/2}`
  and `δ_{P̄'}^{-1/2}` are `factorRestriction`.
- Corollary V.2.3, printed p.294: "l'application `ω ↦ µ^G(ω)µ^{M'}(sω)^{-1}c_{P'|P}(s, ω)` est
  rationnelle et régulière sur `O`." `cWeightedCompactFamily` is this map at convergent points.
  The proof of V.2.3 uses the compact pictures `I^{K×K}_{K∩P×K∩P}(E ⊗ Ě)` and
  `I^{K×K}_{K∩P'×K∩P̄'} I^{K∩M'×K∩M'}_{K∩M'∩s·P×K∩M'∩s·P}(sE ⊗ sĚ)`. The compact pictures here
  are the published `ProductInducedCompactPicture` on `G` at `K` and on `M'` at `K'`. The
  outer `K∩P'×K∩P̄'` level is not represented because only the value at `(1, 1)` is kept.

## Normalizations

Waldspurger I.1 (printed p.240) fixes one special maximal compact `K`: "On munit tout sous-groupe
algébrique fermé `H` de `G` de la mesure invariante par translations à gauche pour laquelle
`mes(H ∩ K) = 1`", and "le groupe `M ∩ K` vérifie relativement à `M` les mêmes propriétés que `K`
relativement à `G`"; in particular `M' ∩ K` is used in `M'`.

- All Haar measures of the integrals of the c-map are the published source measures at `K`
  (`pairQuotientMeasure`, `radicalHaar`, `pairIntersectionHaar`). `γ(G|M')` is the published
  `gammaReal` of `P'` at `K`, defined by the same `K`-normalized measures (`RationalSourceGamma*`).
- The densities are the published `plancherelDensity`: `j_P⁻¹ ∏_α γ(M_α|M)²`, where the
  `γ(M_α|M)` and the canonical scalar `j_P` are formed with the measures normalized by the compact
  subgroup stored in the package (`PG.K`, resp. `PM.K`). `CommonCompactNormalization` makes these
  `K` and `K ∩ M'(F)`, so that the c-map and both densities use the single source normalization,
  as in V.2.2–V.2.3 (printed pp.293–294). See the Markdown of `DynamicOrbitPlancherelWeight` for
  the comparison of `µ^G` and `µ^{M'}` and that of `RationalWeakExpansionTargets` for the norm
  comparison of Lemma V.2.2, where the constants `c(G|M)` and `c(M'|s·M)` enter. These constants
  do not enter the c-family.

## Dependence on the representative

Every object depends on the chosen `n`, and not only through its Weyl class. If `n` is replaced by
another lift `na` of the same relative Weyl element (`a ∈ M_∅(F) = Z_G(T)(F) ⊆ M_I(F)`), then `λ(s)` changes on the two factors by the normalized-induction
covariance: by `δ_P(a)^{-1/2} π(a)^{-1}` and `δ_P(a)^{-1/2} π̌(a)^{-1}`. The two `π(a)` factors cancel
under the pairing that defines the lower coefficients, but `δ_P(a)^{-1}` survives. For
`G = GL₂`, `M = T`, `s = 1`, `a = diag(ϖ, 1)` it is the residue cardinality. Therefore the targets
module (`RationalWeakExpansionTargets`) states the pointwise expansion and the packet identity
only for representative systems whose lifts lie in `K` (premise `LiftsInCompact`), as in the
source, where the representatives of Weyl elements are taken in the fixed special maximal compact
subgroup. Such systems exist whenever `K` has the published property `HasWeylRepresentatives`
(Renard, Théorème V.5.1(2)). Two `K`-lifts of one Weyl element differ by `a ∈ M_∅(F) ∩ K`, for
which `δ_P(a) = 1`, so the summands do not depend on the choice of `K`-lift. The definitions in
this module are stated for every `n`.

## Status

- Imported proofs and constructions: `inductionConjugationIsoApp`, `normalizedInductionLeviEquiv`,
  `StandardIntertwining.fullSourceIntertwiner`, `pairQuotientMeasure(_isCompatible)`,
  `radicalHaar`, `pairIntersectionHaar`, `RealizedLeviStages.inductionInStagesIso`,
  `normalizedInductionEquivOfEquiv`, `contragredientPullbackIso`,
  `normalizedProductInductionTensorEquiv`, `compactSpace_leftQuotient_of_compact_representatives`,
  `RationalDynamicSource.gammaReal`, `productInducedCoefficientTransport`,
  `productInducedCompactEquiv`, `plancherelDensity`, `rationalUnramifiedCharacterRestrict`,
  `unramifiedCharactersHomeomorph`, `parameterTransport`, `rationalFunction_value_eq`,
  `DynamicOppositeCanonicalScalar.radical_unimodular`, `SubgroupFunctor.map_comap`; from Task 7454
  units: `conjugatedCocharacter_dynamic`, `lowerCocharacter_dynamic`, `lowerLeviConjugation`
  (Worker 614), `auxiliaryParabolic_geometry`, `auxiliaryCocharacter`
  (`RationalWeakExpansionAuxiliaryParabolics`, Worker 614),
  `squaredModulus_of_centralSplitTorusCharacter` (`DynamicCommonLeviSquaredModulus`, Worker 614),
  `lowerUnramifiedCharacterConjugation`, `LowerDensityPackage`
  (`RationalWeakExpansionLowerOrbit`), `DensityPackage` (`DynamicOrbitPlancherelWeight`).
- New definitions: `evalOneLinear`, `factorTranslation`, `FactorConverges`, `factorIntertwiner`,
  `conjugateRep`, `factorRestrictionAux`, `factorRestriction`, `restrictedConjugateEquiv`,
  `cFactor`, `CConverges`, `cDualFactor`, `cMap`, `cDomain`, `twistPullbackEquiv`, `cFamily`,
  `cCompactFamily`, `rationalValueAt`, `packageDensity`, `standardLeviUnramifiedRestrict`,
  `CommonCompactNormalization`, `cWeightedDomain`, `cWeightedCompactFamily`.
- New proved lemmas: `mem_conjugatedParabolic_iff`, `mem_conjugatedRadical_iff`,
  `mem_conjugatedLevi_iff_of_centralizer_eq`, `outer_isRepresentedBy`, `centralizer_auxiliary`,
  `auxiliary_realization`, `auxiliaryLevi_conj_iff`, `outerCentralizer_pos`,
  `outerCentralizer_neg`, `rationalValueAt_eq`.
- No targets and no new premises. The convergence conditions are domains of definition.
- Implementation note: `factorRestriction` raises `maxHeartbeats` to 1600000, because the
  induction-in-stages type is large. No proof uses `sorry` or new axioms.
