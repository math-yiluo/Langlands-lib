# The conjugated representation `sπ`, its orbit `sO` and the lower density `µ^{M'}`

Author: Worker 131, task `b2eba110-082e-4b07-9076-f64b90cd0dc3` (Task 7454, revision 1).

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeakExpansionLowerOrbit`,
namespace `Langlands.HarishChandraSchwartz.WeakExpansion`. Four generic declarations about `X`
and `Im X` (`unitaryUnramifiedCharacters_congr`, `unitaryUnramifiedCharactersCongr`,
`unramifiedCharacters_congr`, `unramifiedCharactersCongr`) are in
`Langlands.HarishChandraSchwartz`.

## Purpose

Item 2 of Task 7454 asks, for each `s ∈ W(M'|G|M)`, for the conjugated representation `sπ` of
`(s·M)(F)` and its orbit `sO`. Item 3 asks for the lower densities `µ^{M'}` on `sO`. The packet
identity also needs the transport of measures along `χ ↦ sχ`. This module provides all of these on
the actual groups, for a fixed representative `n ∈ N_G(S)(F)` of `s`:

- `M = M_I`, with `M_I(F)` written `𝐌`, the literal subgroup `standardLeviPoints i ν I` of
  `G(F)`. This is the same presentation as `standardLeviPlancherelWeight` (`µ^G`) and Task 7452.
- `M' = Standard.leviScheme i ν I'`, the actual standard Levi scheme of `I'`.
- `s·M` is the literal Levi `levi χ_s` of the cocharacter `χ_s = lowerCocharacter i ν I' ζ n` of
  `M'`. Here `ζ` is a standard cocharacter of `I` and `χ_s = (n·ζ) ∘ leviTorusHom`. The module
  `RationalWeakExpansionLowerGeometry` proves that the dynamic parabolic, Levi and radical of
  `χ_s` are `M' ∩ nP_In⁻¹`, `M' ∩ nM_In⁻¹` and `M' ∩ nU_In⁻¹`. It also supplies the conjugation
  `e = lowerLeviConjugation … : M_I(F) ≃ₜ* (s·M)(F)`, `m ↦ n m n⁻¹`.

No transport to standard data of `M'` is used: `M' ∩ s·P` is kept as the semistandard dynamic
parabolic of `χ_s`, as in the source.

## Data

- `F`, a nonarchimedean local field in universe `u`. The representation carrier universe `uV` is
  independent of `u`.
- `G` connected reductive (`hG`), `i : T ⟶ G` a maximal split torus (`hi`), `ν` a generic
  cocharacter (`hν`), finite sets of simple roots `I` and `I'`, and `ζ` a standard cocharacter
  of `I` (`hζ`). These are the data of `µ^G`.
- `n : normalizerPoints i` with `hn : conjugatedLevi i ν I n ≤ standardLevi i ν I'` (`n M_I n⁻¹ ⊂
  M'`). For a Weyl index `s`, `Representatives.normalizer s` and `Representatives.levi_le s` of
  `RationalWeakExpansionWeyl` supply them.
- `C`, a normal central subgroup of `𝐌`, and a Haar measure `μ` on `𝐌/C`. Here **`𝐌/C` is
  assumed to carry its Borel σ-algebra (`[BorelSpace (𝐌 ⧸ C)]`)**. Task 7452 and `µ^G` take an
  arbitrary `MeasurableSpace` instance. The Borel condition is needed to carry the Haar measure
  to `(s·M)(F)/sC` (Mathlib's `ContinuousMulEquiv.isHaarMeasure_map`). Haar measures are Borel
  measures, so this narrows only the formal generality, not the source situation.
- `π`, an irreducible admissible representation of `𝐌` that is square integrable modulo `C`
  (`hsq`).
- For `µ^{M'}`, the two global statements `hRefl` and `hCST` that `µ^G` also takes, and a
  `LowerDensityPackage`.

## Definitions and results

### The conjugated Levi scheme

- `lowerCocharacter_comp_leviHom` and `range_centralizerHom_le_leviHom` (proved). In `G`, `χ_s`
  is `(n·ζ) ∘ i`. By `hn`, its centralizer in `G` lies in `M'`.
- `lowerCentralizerFactor` (new definition) is the factorization of the centralizer scheme of
  `χ_s` in `G` through `M'`, made with the published `IsRepresentedBy.factorHom`.
  `lowerCentralizerFactor_comp` is proved.
- `lowerParameterIso₁` (new definition) identifies the centralizer scheme of `χ_s` in `M'` with
  the one in `G`. It uses `isoOfIsRepresentedBy` and the published
  `Dynamic.isRepresentedBy_factorHom_centralizer`. `lowerParameterIso₁_hom_comp` is proved.
- `lowerParameterIso₂` (new definition) identifies the centralizer scheme of `ζ ∘ i` with that of
  `χ_s` in `G` by the inner automorphism `Int(n)`. It uses `IsRepresentedBy.isoOfComap` and
  `Dynamic.centralizer_eq_comap_of_iso`.
- `lowerParameterIso` (new definition) is the composite
  `parameterScheme χ_s ≅ Standard.leviScheme i ν I`, ending with the published
  `standardLeviParameterIso`. `lowerParameterIso_hom_comp` (proved) states that over `G` it is
  `x ↦ n⁻¹ x n`.
- `leviRationalPointHomeomorph_lowerParameterIso` (proved) states that on rational points it is
  `e⁻¹`, composed with the published identifications `parameterHomeomorph` and
  `leviRationalPointHomeomorph`.

### Characters

- `map_lowerParameterIso_mem_iff` (proved) states that the scheme isomorphism preserves and
  reflects the norm-one subgroups defined by all rational characters. It uses the published
  `rationalCommonNormKernel_le_comap` in both directions.
- `commonNormKernel_lowerTransport` (proved) is `(s·M)(F)¹ = e(M_I(F)¹)`. The left side is the
  common kernel of the norms of the rational characters of the centralizer scheme of `χ_s`
  (`leviNormCharacters χ_s`). The right side is the transport along `e` of those of `M_I`
  (`leviRationalNormCharacters i ν I`).
- `unitaryUnramifiedCharacters_congr` and `unitaryUnramifiedCharactersCongr` (proved, generic):
  norm families with the same common kernel have the same `Im X`.
- `unramifiedCharacters_congr` and `unramifiedCharactersCongr` (proved, generic): the same for
  all unramified characters `X`.
- `lowerCharacterConjugation` (new definition) is the map `χ ↦ sχ`,
  `Im X(M_I) ≃ₜ* Im X(s·M)`. `lowerCharacterConjugation_apply` (proved by `rfl`) states that
  `(sχ)(m') = χ(n⁻¹ m' n)`.
- `lowerUnramifiedCharacterConjugation` (new definition) is the same map on all unramified
  characters, `X(M_I) ≃ₜ* X(s·M)`, with `lowerUnramifiedCharacterConjugation_apply` (proved by
  `rfl`). The c-family is defined by convergent integrals only at non-unitary parameters, so it
  needs `z ↦ sz` there too.

### `sπ`, `sC`, `sμ`, `sO`

- `lowerCentral` is `sC = e(C)`. `lowerCentral_normal` and `lowerCentral_le_center` are proved,
  and `lowerCentral_map_symm` states that `e⁻¹(sC) = C`.
- `lowerQuotientEquiv` is the published `quotientContinuousMulEquiv` for `e⁻¹`. The quotient
  `(s·M)(F)/sC` gets its Borel σ-algebra (`lowerQuotientMeasurableSpace`,
  `lowerQuotientBorelSpace`).
- `lowerMeasure` is `sμ`, the image of `μ` under the inverse quotient isomorphism. It is a Haar
  measure (`lowerMeasure_isHaarMeasure`), and `lowerMeasure_map` states that its image back is
  `μ`.
- `lowerRepresentation` is `sπ = π ∘ e⁻¹`, that is `sπ(m') = π(n⁻¹ m' n)` on the space of `π`,
  made with the published `IrreducibleAdmissibleRep.pullback`.
  `lowerRepresentation_isSquareIntegrable` is proved from the published
  `isSquareIntegrableModCentralSubgroup_comp_iff`. So `hsq` is the only representation premise,
  as the task requires.
- `lowerClass` is `ω ↦ sω`, the published `DiscreteSeriesClass.pullback`.
  `lowerClass_smul` states `s(ω ⊗ z) = sω ⊗ sz`, and `lowerClass_discreteSeriesClass` states
  that the class of `π` goes to the class of `sπ`.
- `lowerOrbitMap : O → sO` (new definition), where `O` is the orbit of `π` under `Im X(M_I)` and
  `sO` the orbit of `sπ` under `Im X(s·M)`. `lowerOrbitMap_orbitMap` states
  `s(π ⊗ z) = sπ ⊗ sz` on the orbit parameterizations.
- `finite_lowerStabilizer` (proved): if the unitary stabilizer of `π` is finite, so is that of
  `sπ`. This is the finiteness instance the wave-packet constructions need.

### The lower density and the transported measure

- `lowerAmbient_isConnectedReductive` (proved, from the published
  `standardLevi_isConnectedReductive`) states that `M'` is connected reductive.
- `lowerTorus_isMaximalSplitTorus` (proved, from the published
  `Standard.isMaximalSplitTorus_leviTorusHom`) states that `Standard.leviTorusHom i ν I'` is a
  maximal split torus of `M'`. `DynamicOrbitPlancherelWeight` requires this condition for its
  package weight to be Waldspurger's `µ`.
- `LowerDensityPackage` is the explicit hypothesis package `DensityPackage` of
  `DynamicOrbitPlancherelWeight`, for `H = M'`, `j = Standard.leviTorusHom i ν I'` and the
  cocharacter `n·ζ` of `T`, with `A = sπ`. Its fields are the compact open subgroup of `M'(F)`,
  the Iwasawa decompositions of `M'(F)` for `M' ∩ s·P` and its opposite, the forward and reverse
  continuations, the convergence domains, the generic irreducibility domain and the unitary
  regularity of `j⁻¹`. **The top-level data of `µ^G` do not supply these.** They concern
  induction from `s·M` to `M'`, whereas the data of `µ^G` concern induction from `M_I` to `G`.
- `lowerPlancherelWeight P : sO → ℂ` is `µ^{M'}`, the published-style `orbitPlancherelWeight` of
  the package.
- `lowerCharacterMeasure ρ` is the image of a measure `ρ` on `Im X(M_I)` under `χ ↦ sχ`. Applied
  to the source-normalized character measure `standardLeviUnitaryUnramifiedCharacterHaar`, it
  gives the measure on `Im X(s·M)` used on p.304.

## Comparison with the source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après Harish-Chandra*,
J. Inst. Math. Jussieu 2 (2003), 235–333 (literature id `waldspurger-2003-plancherel`). Page
numbers are printed pages.

- V.1, printed p.288 defines, for `s ∈ W(M'|G|M)`, the map
  "`c_{P'|P}(s, ω) : L(ω, P) → I^{G×G}_{P'×P̄'} L^{M'}(sω, M' ∩ s·P)`". The source writes `sE`
  for the space of `sω`, on which `M` acts through `s⁻¹`. `lowerRepresentation` is exactly this
  representation `m' ↦ π(n⁻¹ m' n)` of `(s·M)(F) = n M(F) n⁻¹`, for the chosen representative.
- VI.3.1, printed p.304: "Pour `s ∈ W(M'|G|M)`, notons `sO` l'orbite de `sω` sous
  `Im X(s·M)`". The later integral is over `Im X(s·M)`, with integrand
  `µ^{M'}(sω ⊗ χ) φ(s⁻¹χ)`. `discreteSeriesOrbit … (class of sπ)` is this orbit, and
  `lowerCharacterConjugation` is `χ ↦ sχ`. The measure on `Im X(s·M)` that turns the integral over
  `Im X(M)` into this one is the image measure `lowerCharacterMeasure`.
- V.2, printed p.292 defines `µ^{M'}` with the same formula as `µ = µ^G`, in the ambient group
  `M'` and for the Levi `s·M`. See the Markdown of `DynamicOrbitPlancherelWeight` for the
  normalization comparison with `µ^G`. The constants `γ(G|M')` and `c(G|M)` do not enter either
  density.

**Dependence on the representative.** Every object here depends on the chosen `n`. A different
representative `n' = n t` with `t` in the centralizer of the torus changes `e` by an inner
automorphism of `M_I(F)`. Then `sπ` changes to an isomorphic representation and `sO` to the same
set of classes. This module does not prove that independence. The targets of the task are stated
for the fixed representative system `Representatives` of `RationalWeakExpansionWeyl`.

## Status

- Imported proofs and constructions: `IsRepresentedBy.factorHom`/`factorHom_comp`,
  `isoOfIsRepresentedBy`, `isoOfComap`, `Dynamic.isRepresentedBy_factorHom_centralizer`,
  `Dynamic.centralizer_eq_comap_of_iso`, `standardLeviParameterIso`, `rationalPoints_map_innerIso_inv`,
  `rationalCommonNormKernel_le_comap`, `leviRationalNormCharacters_apply_points`,
  `unitaryUnramifiedCharactersHomeomorph`, `unramifiedCharactersHomeomorph`,
  `quotientContinuousMulEquiv`,
  `isSquareIntegrableModCentralSubgroup_comp_iff`, `IrreducibleAdmissibleRep.pullback`,
  `DiscreteSeriesClass.pullback`(`_injective`), `SmoothDualClass.pullback_twist`,
  `ContinuousMulEquiv.isHaarMeasure_map`, `standardLevi_isConnectedReductive`,
  `Standard.isMaximalSplitTorus_leviTorusHom`, and from the earlier units of Task 7454 (`RationalWeakExpansionLowerGeometry`, `DynamicOrbitPlancherelWeight`)
  `lowerCocharacter`, `lowerLeviConjugation`, `conjugatedCocharacter_dynamic`,
  `DensityPackage` and `orbitPlancherelWeight`.
- New definitions: `unitaryUnramifiedCharactersCongr`, `unramifiedCharactersCongr`,
  `lowerCentralizerFactor`, `lowerParameterIso₁`, `lowerParameterIso₂`, `lowerParameterIso`,
  `lowerCharacterConjugation`, `lowerUnramifiedCharacterConjugation`,
  `lowerCentral`, `lowerQuotientEquiv`, `lowerMeasure`, `lowerRepresentation`, `lowerClass`,
  `lowerOrbitMap`, `LowerDensityPackage`, `lowerPlancherelWeight`, `lowerCharacterMeasure`.
- New proved lemmas: all other declarations listed above.
- No targets are stated here. The c-family and the four targets are in later modules.
