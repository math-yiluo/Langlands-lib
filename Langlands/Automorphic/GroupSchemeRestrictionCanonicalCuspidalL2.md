# Cuspidal `L²` spaces of the canonical quotient `[G]`

Author: Worker 112.

Getz--Hahn (`getz-hahn-2024-automorphic-representations`) define
`[G] = A_G G(F) \ G(A_F)` in (2.20)--(2.21), printed pp. 68--69. Their
Definition 6.5.1 and (6.18), printed p. 167, call an automorphic form
cuspidal when its integral over `[N]` vanishes for the unipotent radical `N`
of every proper parabolic and every `g`. Their (6.20)--(6.21), printed
p. 168, define `L²_cusp([G])` by the same vanishing almost everywhere.

Three published modules build such spaces on the restriction quotient
`Quotient F G S j`, for a supplied `j : S.toGrp ⟶ AffineWeil.groupScheme ℚ F G`
and a supplied measure:
- `GroupSchemeRestrictionCuspidalL2` gives the continuous functions whose
  constant terms vanish everywhere, and the continuous functions coming from
  the published `AdelicCuspidalForms`, both as `L²` classes;
- `GroupSchemeRestrictionFullAEL2` gives the almost-everywhere cuspidal
  subspace;
- `GroupSchemeRestrictionFullAEL2Hilbert` gives its closedness, orthogonal
  projection and intertwining projection.

The published `AdelicRestrictionSplitCentreCanonical` fixes one split
component `j₀` of `Res_{F/ℚ} G` and one split component `i₀` of `G`. It
defines `CanonicalQuotient F G = Quotient F G S₀ j₀` with measure
`canonicalMeasure F G = quotientHaarMeasure F G S₀ j₀`. For every split
component `j` of the restriction it also gives the measure-preserving
identification `toCanonicalQuotient hj` and the `L²` isometry
`toCanonicalL2Equiv hj`.

This module does two things:
- it specializes the three constructions to `CanonicalQuotient F G`, so that
  they depend only on `F`, `G` and the analytic parameters;
- it proves that `toCanonicalL2Equiv hj` carries each space built from any
  split component `j` onto the canonical one. So the spaces do not depend on
  which split component of the restriction is used.

## Data

- `F : Type` is a number field.
- `G` is a group scheme over `Spec F` whose underlying scheme is affine and
  locally of finite type.
- In the transport section: a commutative group scheme `S` over `ℚ` and
  `j : S.toGrp ⟶ AffineWeil.groupScheme ℚ F G` with `hj : IsSplitComponent j`.
- For parabolic vanishing: the explicit `hPD : ParabolicDynamicStatement`,
  `hG : IsConnectedReductive G`, and supplied measures `measuresU` on the
  published all-proper-parabolic radical quotients.
- For `AdelicCuspidalForms`: the published parameters `Kinf`, `rho`,
  `hsmooth`, `hcalc`, `hPD`, `hG`, `hrho`, `hK` and `hN`.
- In the canonical section, also
  `hCST : CentralSplitTorusCharacterStatement.{0}`. This is the published
  proposition that, over every field, every nonzero rational character of a
  connected reductive group restricts nontrivially to some central split
  torus. It is not proved in the Library at commit `2816ea5d`. The canonical
  module needs it for injectivity of character restriction along `i₀`, and
  through that for right invariance and positivity of `canonicalMeasure`.

## Transport from any split component of the restriction

Write `e = toCanonicalQuotient hj`. It is the identity on representatives,
from `Quotient F G S j` to `CanonicalQuotient F G`.

- `continuousToCanonical hj` is the linear equivalence
  `C(Quotient F G S j, ℂ) ≃ₗ[ℂ] C(CanonicalQuotient F G, ℂ)` given by
  `f ↦ f ∘ e⁻¹`. Its two apply lemmas give the formulas.
- `quotientContinuousPullback_continuousToCanonical`: the published pullback
  to `G(A_F)` of `continuousToCanonical hj f` for the canonical data equals
  the pullback of `f` for `(S, j)`. It uses `toCanonicalQuotient_mk`.
- `continuousToCanonical_rightAction`: the equivalence intertwines the two
  published `continuousQuotientRightAction`s, by
  `toCanonicalQuotient_rightTranslate`.
- `memLp_continuousToCanonical_iff`: `continuousToCanonical hj f` is square
  integrable for `canonicalMeasure F G` exactly when `f` is for
  `quotientHaarMeasure F G S j`. It uses
  `measurePreserving_toCanonicalQuotient`.
- `quotientContinuousL2ToLp_continuousToCanonical`: the `L²` class of the
  transported function is `toCanonicalL2Equiv hj` of the class of `f`. It
  holds by definition.
- `toCanonicalL2Equiv_splitComponentL2Equiv`: for any split component `i` of
  `G`, `toCanonicalL2Equiv hj` composed with the published
  `splitComponentL2Equiv F G hj hs` is `splitComponentL2Equiv F G hj₀ hs`.
  The proof composes the two pullbacks and checks the maps on
  representatives.

The next results take arbitrary right-invariance proofs `hInv` for
`quotientHaarMeasure F G S j` and `hInv'` for `canonicalMeasure F G`.

- `continuousToCanonical_mem_parabolicCuspidalL2_iff`: the equivalence
  matches the two published `quotientParabolicCuspidalL2Subrepresentation`s.
- `parabolicCuspidalL2FunctionsToCanonical` is the resulting linear
  equivalence of the carriers `QuotientParabolicCuspidalL2Functions`.
  `parabolicCuspidalL2FunctionsToCanonical_rightAction` proves that it
  intertwines the right actions.
- `quotientParabolicCuspidalL2ToLp_parabolicCuspidalL2FunctionsToCanonical`:
  on `L²` classes it is `toCanonicalL2Equiv hj`.
- `toCanonicalL2Equiv_mem_parabolicCuspidalL2Image_iff`:
  `toCanonicalL2Equiv hj φ` lies in the published
  `quotientContinuousParabolicCuspidalL2Image` for `canonicalMeasure F G`
  exactly when `φ` lies in it for `quotientHaarMeasure F G S j`.
- `continuousToCanonical_mem_cuspidalFormL2_iff`,
  `cuspidalFormL2FunctionsToCanonical`,
  `cuspidalFormL2FunctionsToCanonical_finiteRightAction`,
  `quotientCuspidalFormL2ToLp_cuspidalFormL2FunctionsToCanonical` and
  `toCanonicalL2Equiv_mem_cuspidalFormL2Image_iff` are the same statements
  for the published `quotientCuspidalFormL2Subrepresentation` and
  `quotientCuspidalFormL2Image`, with the action of the finite adelic points.

## Canonical spaces

Assume `hCST`, `hPD` and `hG`.

### Continuous parabolic vanishing

- `canonicalParabolicCuspidalL2Image F G hCST hPD hG measuresU` is the
  published `quotientContinuousParabolicCuspidalL2Image` for
  `canonicalMeasure F G`, with the published invariance
  `canonicalMeasure_rightInvariant`. It is a subrepresentation of the
  published `canonicalL2RightAction F G hCST hG`.
- `canonicalParabolicCuspidalL2ToLp_injective`: distinct continuous
  parabolic-vanishing functions have distinct canonical `L²` classes. It uses
  `canonicalMeasure_isOpenPosMeasure`.
- `toCanonicalL2Equiv_mem_canonicalParabolicCuspidalL2Image_iff`: for any
  split component `j` of the restriction and any right-invariance proof
  `hInv`, `toCanonicalL2Equiv hj` carries the image for `(S, j)` onto
  `canonicalParabolicCuspidalL2Image`.

### `AdelicCuspidalForms`

- `canonicalCuspidalFormL2Image F G hCST Kinf rho hsmooth hcalc hPD hG hrho hK hN`
  is the published `quotientCuspidalFormL2Image` for `canonicalMeasure F G`.
  It is a subrepresentation of the published
  `rationalQuotientL2FiniteRightAction`, the restriction of the canonical
  right regular representation to the finite adelic points.
- `canonicalCuspidalFormL2ToLp_injective` and
  `toCanonicalL2Equiv_mem_canonicalCuspidalFormL2Image_iff` are the
  injectivity and independence statements, as above.

### Almost-everywhere cuspidal subspace

Each definition here is the published split-component construction at
`j₀` and `i₀`. Its hypotheses on `characterRestrict i₀` are supplied by the
published `canonical_characterRestrict_injective` (from `hCST` and `hG`) and
`canonical_finiteIndex` (from `hG`).

- `canonicalFullAEL2CuspidalSubmodule F G hCST hPD hG` is the published
  `splitComponentFullAEL2CuspidalSubmodule`, a subspace of
  `Lp ℂ 2 (canonicalMeasure F G)`.
- `mem_canonicalFullAEL2CuspidalSubmodule`: its carrier is the published
  intrinsic locus `quotientFullAEL2CuspidalLocus` of the canonical data. An
  `L²` class belongs when, for every proper rational parabolic, the constant
  term of its chosen representative converges and vanishes for almost every
  element of the norm-one subgroup.
- `mem_canonicalFullAEL2CuspidalSubmodule_iff`: `φ` belongs exactly when
  `(canonicalL2Equiv F G).symm φ` lies in the published positive-torus locus
  `fullAEL2CuspidalLocus` of `i₀`.
- `isClosed_canonicalFullAEL2CuspidalSubmodule`: the subspace is closed.
- `canonicalFullAEL2CuspidalSubrepresentation` is the subspace as a
  subrepresentation of `canonicalL2RightAction F G hCST hG`.
- `canonicalFullAEL2CuspidalOrthogonalProjection` is the orthogonal
  projection of `L²([G])` onto the subspace, and
  `canonicalFullAEL2CuspidalProjectionIntertwiner` is that projection as an
  intertwining map onto the subrepresentation.
- `toCanonicalL2Equiv_mem_canonicalFullAEL2CuspidalSubmodule_iff`: for any
  split component `j` of the restriction, `toCanonicalL2Equiv hj φ` lies in
  the canonical subspace exactly when `φ` lies in the intrinsic locus
  `quotientFullAEL2CuspidalLocus F G hPD hG S j (quotientHaarMeasure F G S j)`.
  The proof passes through the chosen component `i₀` of `G`: by the published
  `mem_splitComponentFullAEL2CuspidalSubmodule_iff`, both memberships are
  equivalent to membership of the same positive-torus class in
  `fullAEL2CuspidalLocus`. It uses
  `toCanonicalL2Equiv_splitComponentL2Equiv` to identify the two classes.

## Scope and what is not claimed

- The chosen split component `j₀` of `Res_{F/ℚ} G` is not shown to agree
  with the greatest `ℚ`-split torus of `Res_{F/ℚ} Z_G` used by Getz--Hahn.
- Every result of the canonical section depends on `hCST`, which is not
  proved in the Library at commit `2816ea5d`. The transport section does not
  use it.
- The images of continuous functions are algebraic ranges. They are not
  asserted to be closed, dense, or equal to the almost-everywhere subspace.
  Theorem 6.5.3 of Getz--Hahn (density of cusp forms in `L²_cusp([G])`,
  printed p. 169) is not claimed. `AdelicCuspidalForms` is not identified
  with the literal Getz--Hahn cusp forms.
- As in the published `GroupSchemeRestrictionFullAEL2`, the
  almost-everywhere variable is the norm-one subgroup with its Haar measure,
  and the measure on `[N_P]` is the published mass-one quotient measure.
  Getz--Hahn quantify over `A_G \ G(A_F)` with a Haar measure. Agreement of
  the two conditions is not proved here.
- Nothing here concerns finite volume, reduction theory, discreteness of the
  cuspidal spectrum or trace-class properties (Getz--Hahn Theorem 9.1.2).

## Provenance

This is an internal construction. Every definition specializes a published
construction to the canonical quotient. Every theorem either specializes a
published theorem or transports a published object along the published
identification `toCanonicalQuotient`. The Getz--Hahn passages above are cited
for the objects being implemented. No new external theorem is asserted.
