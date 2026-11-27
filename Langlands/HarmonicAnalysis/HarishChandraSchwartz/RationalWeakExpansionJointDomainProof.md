# The joint convergence domain of the c-family has nonempty interior (proof)

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeakExpansionJointDomainProof`,
namespace `Langlands.HarishChandraSchwartz.WeakExpansion`.

## Purpose and status

The module `RationalWeakExpansionJointDomain` states `CDomainInteriorNonemptyStatement`: for the
data of the weak-expansion targets, with the quotient `M_I(F)/C_M` carrying its Borel σ-algebra
(the instance binder `[BorelSpace (𝐌 ⧸ C_M)]` of the statement) and a Haar measure `μ` on it,
if `π` is square integrable modulo `C_M` for `μ`, `K` is the special
maximal compact subgroup and an Iwasawa complement of the standard minimal parabolic, then the
joint convergence domain `cDomain … n hn K hKc π.obj` of the two standard integrals
`J_{P_s|s·P}` (on `ⁿ(π ⊗ z)`) and `J_{P̃_s|s·P}` (on `ⁿ((π ⊗ z)ˇ)`) has nonempty interior.

- **Theorem `cDomainInteriorNonempty`** proves `CDomainInteriorNonemptyStatement` for all its
  data: the same binders, with independent universes `u` (field) and `uV` (representation
  carrier), and no further hypotheses.
- Its axioms are `propext`, `Classical.choice` and `Quot.sound`.

Together with `cWeightedDomain_interior_nonempty_of_cDomain` (module
`RationalWeakExpansionJointDomain`), this gives the field `interior_nonempty` of
`WeightedCExtension`. This module proves neither `WeightedCRegularityBorelStatement` nor any
other weak-expansion target.

## Notation

`𝐌 = M_I(F)` (`standardLeviPoints i ν (rootSet i ν I)`), `θ_s = θs` the cocharacter
`conjugatedCocharacter i ζ n` composed with `i`, and `(s·M)(F) = Z_G(θ_s)(F)` the literal dynamic
Levi `DynamicOppositeStandardIntertwining.levi θs`. `ψ₊`, `ψ₋` (`ψpos`, `ψneg`) are the auxiliary
cocharacters `auxiliaryCocharacter i (±ζ') (conjugatedCocharacter i ζ n)` composed with `i`: they
define `P_s` and `P̃_s` and have the same centralizer as `θ_s` (`centralizer_auxiliary`).

## The proof route

The proof moves both integrals of `cDomain` to the common Levi `Z_G(θ_s)` and its own unramified
parameters, finds an explicit convergence threshold for each integral in the root coordinates of
one split component, and shows that the two threshold regions meet in an open set.

### Two generic lemmas

- `map_iso_mem_rationalCommonNormKernel_iff`: an isomorphism of group schemes preserves and
  reflects the common norm kernels `rationalCommonNormKernel`.
- `domain_eq_top_iff_of_levi_eq`: for two literally equal Levi subgroups with semidirect
  decompositions of one parabolic, and a linear equivalence intertwining the two inducing
  representations, full convergence of the standard integral (`StandardIntertwining.domain = ⊤`)
  holds for one if and only if for the other. Proof: `subst` and
  `StandardIntertwining.domain_eq_top_iff_equiv`.

### Conjugation to the Levi of `θ_s` (section `Conjugation`)

- `thetaLevi_conj_mem_iff`, `thetaLeviConjugation`: `m ↦ n m n⁻¹` is a topological group
  isomorphism `M_I(F) ≃ Z_G(θ_s)(F)` (from `mem_conjugatedLevi_iff_of_centralizer_eq`), with
  `thetaLeviConjugation_apply_coe` and `thetaLeviConjugation_symm_apply_coe`.
- `theta_centralizer_comap`, `thetaLeviParameterIso`, `thetaLeviParameterIso_hom_comp`: the
  centralizer scheme of `θ_s` is isomorphic to the standard Levi scheme of `M_I` through
  `Int(n)⁻¹` (`SubgroupFunctor.IsRepresentedBy.isoOfComap` and `standardLeviParameterIso`).
- `leviRationalPointHomeomorph_thetaLeviParameterIso`, `map_thetaLeviParameterIso_mem_iff`,
  `commonNormKernel_thetaTransport`: on points this isomorphism is the inverse conjugation, so the
  norm-one subgroups correspond: `(s·M)(F)¹ = n M_I(F)¹ n⁻¹`.
- `thetaCharacterTransport`: the induced homeomorphic group isomorphism
  `X(M_I) ≃ X(Z_G(θ_s))` of unramified characters, `z ↦ z ∘ e⁻¹`, read in the parameters of the
  centralizer scheme (`parameterTransport`); `parameterTransport_thetaCharacterTransport`
  evaluates it.

### The two factors (section `Factors`)

- `thetaConjugateRep B` is the conjugate `ⁿB = B ∘ e⁻¹` on `Z_G(θ_s)(F)`;
  `thetaConjugateEquivOfIso` transports isomorphisms, and `thetaConjugateTwistEquiv`,
  `thetaConjugateTwistEquiv'` identify `ⁿ(B ⊗ z)` with `ⁿB ⊗ w`, where `w` is the transported
  parameter.
- `thetaLevi_eq_auxiliaryLevi`: the literal Levis of `θ_s` and of `ψ_α` agree.
- `factorConverges_iff`: convergence of one factor of the c-family (`FactorConverges`, on
  `conjugateRep … B`) is full convergence of the standard integral from `P(θ_s)` to `P(ψ_α)` with
  common Levi cocharacter `θ_s` on `thetaConjugateRep B` (by `domain_eq_top_iff_of_levi_eq`).
- `mem_cDomain_of_mem_pairFullDomainRegion`: if the transported parameter `w` of `z` lies in the
  full domain `pairFullDomainRegion θs K hK θs rfl ψ₊ (ⁿA)` and `w⁻¹` lies in
  `pairFullDomainRegion θs K hK θs rfl ψ₋ (ⁿ(Aˇ))`, then `z ∈ cDomain … A`. For the second
  factor, `(A ⊗ z)ˇ ≅ Aˇ ⊗ z⁻¹` (`SmoothRep.contragredientTwistIso`).

### Signs of the split-component roots (section `Sign`)

Fix a split component `a : T_s → Z_G(θ_s)` and presentations
(`DynamicCommonLeviPresentations.ParabolicData`) `dθ`, `dp`, `dm` of `P(θ_s) = s·P`, `P_s` and
`P̃_s` on `a`.

- `torusThetaFactor`, `exists_splitComponent_cocharacter`, `groupHom_auxiliary_comp`,
  `groupHom_zsmul_add_comp`: a cocharacter of the maximal split torus whose centralizer contains
  `Z_G(θ_s)` factors through `a`; this gives cocharacters `θ_T`, `ζ'_T` of `T_s` lifting `θ_s` and
  `ζ'`, and `N ζ'_T + θ_T` lifts the auxiliary cocharacters.
- `pos_iff_of_parabolicData`, `neg_iff_of_parabolicData`: a relative root has positive (negative)
  pairing with the split-component cocharacter of a presentation if and only if it has positive
  (negative) pairing with a lift of the defining cocharacter (by
  `subgroupRelativeRoots_radical` and `subgroupRelativeRoots_dynamicUnipotent`).
- `sign_relation`: a root positive for `s·P` and negative for `P_s` is positive for `P̃_s`.
  Indeed `⟨α, θ_T⟩ > 0`, `⟨α, N₊ζ'_T + θ_T⟩ < 0` force `⟨α, −N₋ζ'_T + θ_T⟩ > 0` for
  `N₊, N₋ ≥ 0`.
- `exists_joint_region_point`: for any two thresholds `R₊`, `R₋` there is a parameter `w` of
  `Z_G(θ_s)` in the strict region `parabolicUnramifiedIntertwiningRegion` of threshold `R₊` for
  the pair (`s·P`, `P_s`) such that `w⁻¹` is in the strict region of threshold `R₋` for
  (`s·P`, `P̃_s`). The first region tests the relative roots `α` with positive pairing with the
  split-component cocharacter of `dθ` (positive for `s·P`) and negative pairing with that of
  `dp` (negative for `P_s`). The second region tests the roots `α` with positive pairing with
  the cocharacter of `dθ` and **negative** pairing with that of `dm` (negative for `P̃_s`). The
  proof forms the set of the roots tested by the first region together with the **negatives**
  `β = −α` of the roots tested by the second region. Every element of this set pairs positively
  with the split-component cocharacter of `dm`: a root of the first region by `sign_relation`,
  and `β = −α` for a root `α` of the second region directly from its defining condition
  `⟨α, dm⟩ < 0`. So `rootThresholdRegion_nonempty_of_positivePairing` (for the Weyl-induced
  nondegenerate form of `dθ`, with the cocharacter of `dm` as positive direction) gives a real
  point `x` whose pairing with every element of the set exceeds `max R₊ R₋`.
  `exists_positiveImageCharacter_extension_of_injective` realizes `x` as the normalized real
  part of an unramified character `w`, which therefore lies in the first region. The inverse
  `w⁻¹` has real part `−x` (`SplitTorus.normalizedRealPart_inv`), so its test value at a root
  `α` of the second region is the pairing of `x` with `−α`, which exceeds `R₋`. Both
  memberships are read through `mem_parabolicUnramifiedIntertwiningRegion`.

### Final assembly (section `Final`)

- `theta_parabolic_mul_compact`: `G(F) = (s·P)(F) K` for special `K`. The Weyl element of `n`
  has a representative `k₀ ∈ K` (`standardLeviIwasawaFactorsAt_and_weylRepresentatives_of_special`).
  `n⁻¹k₀` centralizes the maximal split torus, so `s·P = k₀ P_I(F) k₀⁻¹`, and
  `G(F) = P_I(F) K` (`exists_standardParabolicPoints_rootSet_mul`) gives the decomposition.
- `leviSplitQuotientHaar_isInvInvariant`: every Haar measure on `M_I(F)/C_M` is invariant under
  inversion. `M_I(F)` is unimodular: `RationalPointFamily.rationalReductiveUnimodularity` for the
  connected reductive Levi scheme (`isConnectedReductive_leviScheme_rootSet`), transported along
  `leviRationalPointHomeomorph` (`modularCharacter_continuousMulEquiv`). `C_M` is closed (image
  of the closed `isClosed_range_splitComponent`) and central. The quotient is second countable and
  locally compact, so the measure is regular, and `Haar.centralSubgroupQuotient_isMulRightInvariant`
  and `Langlands.isInvInvariant_of_isMulRightInvariant` conclude.
- `cDomain_interior_nonempty_of_data`: for presentations `dθ`, `dp`, `dm` and opposite data
  `op`, `om` on one split component, assume the conjugates `ⁿB` and `ⁿ(Bˇ)` are admissible and
  unitarizable and `G(F) = (s·P)(F) K`. Then the interior of `cDomain … B` is nonempty.
  `exists_threshold_mem_pairFullDomainRegion_of_data` (module `ActualCommonLeviUnitaryThreshold`)
  gives thresholds `R₊` for `ⁿB` and `R₋` for `ⁿ(Bˇ)`, and `exists_joint_region_point` gives a
  common point `w₀`. The set `V`, the intersection of the first region with the preimage of the
  second region under inversion `w ↦ w⁻¹` (so `w ∈ V` exactly when `w` is in the first region and
  `w⁻¹` in the second), is open (`isOpen_parabolicUnramifiedIntertwiningRegion` and continuity
  of inversion) and contains `w₀`. Its preimage under
  `thetaCharacterTransport` is an open neighbourhood of the preimage of `w₀` contained in
  `cDomain`, by `mem_cDomain_of_mem_pairFullDomainRegion`.
- `cDomain_interior_nonempty_of_unitarizable`: the same without given presentations. A split
  component of `Z_G(θ_s)` comes from `splitComponentStatement`, the presentations from
  `DynamicCommonLeviPresentations.parabolicData` and `oppositeData`, and finiteness of the
  relative Weyl group from `finite_relativeWeylGroup` applied to `hG`.
- `cDomainInteriorNonempty`: from the three premises. `π` is unitarizable by
  `isUnitarizable_of_isSquareIntegrableModCentralSubgroup`, which uses inversion invariance of
  `μ` (`leviSplitQuotientHaar_isInvInvariant`). `π` is admissible (first component of square
  integrability). Its smooth dual is admissible (`SmoothRep.isAdmissible_contragredient_iff`) and
  unitarizable (the conjugate-linear equivalence `smoothDualEquiv` and
  `isUnitarizable_iff_of_conjugateEquiv`). Conjugation by `e⁻¹` preserves admissibility
  (`isAdmissible_comp_continuousMulEquiv`) and unitarizability. With
  `theta_parabolic_mul_compact`, `cDomain_interior_nonempty_of_unitarizable` applies.

## Relation to the source

Source: J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, registered as
`waldspurger-2003-plancherel` (SHA-256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`); PDF page = printed
page − 234.

- Théorème IV.1.1 (printed p.278): for `π` of finite length there is `R` such that
  `J_{P'|P}(π ⊗ χ)` is defined by convergent integrals when `⟨Re χ, α⟩ > R` for all
  `α ∈ Σ(P) ∩ Σ(P̄')`. The thresholds used here have this shape. They come from the
  bounded-coefficient version in `ActualCommonLeviUnitaryThreshold`, not from IV.1.1 itself.
- V.1 (printed pp.288–289): `c_{P'|P}(s, ω)` is built from `J_{P_s|s·P}(sω)` and
  `J_{P̃_s|s·P}(sω̌)`.

Simultaneous convergence of the two integrals on a nonempty open set is **derived**: the
source works with the rational continuations and does not state it. The proof follows the plan
in the Markdown of `RationalWeakExpansionJointDomain`. The direction `−ζ'` of that plan is
replaced by the split-component cocharacter of the presentation `dm` of `P̃_s`. It pairs
positively with the roots tested by the first region, by `sign_relation`. It also pairs
positively with the negatives of the roots tested by the second region, by that region's
defining inequality. The second factor is evaluated at the inverse character, whose real part
is `−x`, so the inequalities on these negated roots give the second convergence threshold.

## Imports

`RationalWeakExpansionJointDomain` (the statement, `cDomain`), `ActualCommonLeviUnitaryThreshold`
(the thresholds), `DynamicOppositeConjugationScalar`, `RationalWeakExpansionSpecialCompact`,
`Representation.Unitary.ConjugateEquiv`, `CentralSubgroupQuotientHaar` (quotient right
invariance) and `RationalInducedOrbitWavePacket` (`isConnectedReductive_leviScheme_rootSet`). No
axioms, no `sorry`.
