# Adapters from the VIII.4 targets to the actual orbit central-character fiber

The published targets of `RationalCuspidalCentralStatements`, and the
lower-inclusion statement of `RationalCuspidalLowerInclusionStatement`,
use three conventions:

- a continuous character `χ : A_G →* ℂˣ` with `IsUnitaryCharacter χ`, and
  Waldspurger's `p_χ` as `centralProjection`;
- the predicate `classActsByCharacter A_G χ` for `E₂(G)_χ`;
- a split component `s` with `IsSplitComponent s`.

The `M = G` packet calculation of `RationalOrbitCentralProjection`
(Waldspurger, proof of Theorem VIII.4.2, printed p.330, PDF p.96) and the
isolation of `RationalOrbitFiberIsolation` use different conventions:

- a circle-valued character `η : A_G →* Circle`;
- the orbit fiber `rationalOrbitCentralFiber`, defined by the published
  central character `rationalOrbitCentralCharacter`;
- the premise `(RenardCartan.splitValuationImage s).FiniteIndex`.

This module proves the three conversions. Each is a derived interface
statement about existing definitions; no new analytic input is used.

## Characters

- `unitaryCircleCharacter χ hχ` (definition): for a group `A`, a
  homomorphism `χ : A →* ℂˣ` and `hχ : ∀ a, ‖χ a‖ = 1`, the same values
  as a homomorphism into the unit circle. `coe_unitaryCircleCharacter`
  states that its complex values are those of `χ`.
  `continuous_unitaryCircleCharacter` gives continuity from continuity of
  `χ`. The target's `IsUnitaryCharacter χ` provides `hχ` as
  `hχ.norm_eq_one`.
- `centralProjection_eq_integral_unitaryCircleCharacter`: for a subgroup
  `A` of a group `Γ` and any measure `μA`,
  `centralProjection μA χ f g = ∫ a, η(a⁻¹) f(a g) dμA` with
  `η = unitaryCircleCharacter χ hχ.norm_eq_one`. The integrands agree
  pointwise because `η(a⁻¹) = χ(a)⁻¹`. This is the left side of
  `integral_central_rationalOrbitWavePacket`.

## Classes and the fiber

- `discreteSeriesCentralRestriction_eq_unitaryCircleCharacter_iff`: for a
  topological group `G`, a normal central subgroup `A`, a Haar measure on
  `G/A` and a discrete-series class `ω` with carriers in universe `uV`, the
  published `discreteSeriesCentralRestriction A hA μ A hA ω` equals
  `unitaryCircleCharacter χ hχ` if and only if
  `classActsByCharacter A χ ω.val`. On a representative `π`, the
  published `discreteSeriesCentralCharacter` acts by scalars on the centre
  (`discreteSeriesCentralCharacter_hasCentralCharacter`). If the
  characters agree on `A`, then `A` acts by `χ`. Conversely, if `A` acts by
  `χ`, both scalars act on a nonzero vector, which exists because an
  irreducible representation is a simple module and hence nontrivial. So
  the scalars agree.
- `mem_rationalOrbitCentralFiber_unitaryCircleCharacter_iff`: in the
  rational setting of `RationalOrbitCentralProjection` (central `s`, any
  measurable structure and Haar measure on `G(F)/A_G`), a class `x` of the
  orbit of `omega` lies in
  `rationalOrbitCentralFiber s hs mu omega (unitaryCircleCharacter χ hχ)`
  exactly when `classActsByCharacter A_G χ x.val.val`. The orbit central
  character is by definition the central restriction of `x.val`, so this
  is the previous result.
- `self_mem_rationalOrbitCentralFiber_unitaryCircleCharacter_iff`: the
  same for the base point `⟨omega, MulAction.mem_orbit_self omega⟩`. A
  class of `E₂(G)_χ` is in the fiber of its own orbit.

## The finite-index premise

`finiteIndex_splitValuationImage_of_isSplitComponent`: for a connected
reductive `G` over a nonarchimedean local field and a split component
`s`, `(RenardCartan.splitValuationImage s).FiniteIndex` holds. The
published theorem `GroupScheme.centralSplitTorusCharacter` proves
`CentralSplitTorusCharacterStatement`. With it,
`characterRestrict_injective_of_centralSplitTorusCharacter` gives
injectivity of rational-character restriction to `s`. The published
`RenardCartan.finiteIndex_splitValuationImage_of_injective` then gives
finite index. No premise is added.

These results connect the target-side data to the orbit-side data. They
do not construct coefficient sections and do not prove any membership in
the cuspidal Schwartz space.
