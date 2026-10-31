# Affine chart maps into `Proj`

This helper module is used in the proof of
`Langlands.AlgebraicGeometry.LinearSystemMorphismStatement`. It is internal: it is not a
Library statement and has no literature source of its own. It provides the local form of the
description of morphisms into projective space (Stacks Project, Constructions of Schemes, Section 27.14 "Invertible sheaves and morphisms into Proj", Lemma 27.14.1, tag 01NJ, in the registered source `stacks-very-ampleness-support-2026-10-29`; property (1) there, $r^{-1}(D_+(f)) = T_{\psi(f)}$) in the special case needed there: a morphism `T ⟶ Proj A` that factors through one standard affine
chart. Everything is in the namespace `Langlands.AlgebraicGeometry.LinearSystem`.

Throughout, `A` is a commutative ring graded by `𝒜 : ℕ → σ` (`GradedRing 𝒜`).

## The ring map `awayLift`

For a commutative ring `R`, a ring map `e : A →+* R` and an element `t : A` with `e t` a
unit, `awayLift 𝒜 e t hu : Away 𝒜 t →+* R` is the composite of the inclusion of the
degree-zero part `A_(t)` into the localization `A_t` with the map `A_t → R` induced by `e`.

- `awayLift_mk`: for `t ∈ 𝒜 d` and `a ∈ 𝒜 (n • d)`, the fraction `a / t ^ n` is sent to
  `e a * (e t)⁻¹ ^ n`.
- `awayLift_mk_eq_iff`: the image of `a / t ^ n` equals `r` if and only if
  `e a = r * e t ^ n`.
- `awayLift_comp`: composing with a ring map `g : R →+* R'` gives `awayLift` of `g ∘ e`.
- `awayLift_eq_of_scale`: if `t` is homogeneous and `e' a = c ^ m * e a` for every
  homogeneous `a` of degree `m` (a rescaling of `e` by `c` according to degree), then `e` and
  `e'` have the same `awayLift`. The lemma does not require `c` to be a unit, and it allows
  `t` to have degree `d = 0`. In degree zero `c` can fail to be a unit: for `A = R = ℚ` graded
  in degree zero, `t = 1` and `e = e'` the identity, every `c`, including `c = 0`, satisfies
  the hypothesis. If `d > 0` and both `e t` and `e' t` are units, then `c` is a unit, because
  `e' t = c ^ d * e t` makes `c ^ d` a unit.
- `awayLift_comp_awayMap`: compatibility with the localization map `A_(t) → A_(t g)` of
  Mathlib (`HomogeneousLocalization.awayMap`) when `x = t * g`.
- `eq_of_awayLift_eq`: if `e t = e' t` and `e`, `e'` have the same `awayLift`, then `e` and
  `e'` agree on homogeneous elements whose degree is a multiple of `deg t`.
- `awayLift_fromZeroRingHom`: on the image of `A₀` in `A_(t)`, `awayLift` is `e`.

## The chart map `chartMap`

For a scheme `T`, a ring map `e : A →+* Γ(T, ⊤)` and a homogeneous `t ∈ 𝒜 d` with `0 < d`
and `e t` a unit,

`chartMap 𝒜 e ht hd hu := T.toSpecΓ ≫ Spec.map (awayLift 𝒜 e t hu) ≫ Proj.awayι 𝒜 t ht hd`,

the morphism `T ⟶ Spec Γ(T, ⊤) ⟶ Spec A_(t) ≅ D₊(t) ⊆ Proj A`.

- `chartMap_congr`, `chartMap_ringHom_congr`: independence of the degree witness, and
  transport along an equality of ring maps.
- `comp_chartMap` (naturality): for `g : T' ⟶ T`, `g ≫ chartMap e = chartMap (g^# ∘ e)`,
  from the naturality of `toSpecΓ` and `awayLift_comp`.
- `chartMap_eq_of_scale`: rescaling `e` according to degree (as in `awayLift_eq_of_scale`)
  does not change the chart map.
- `chartMap_eq_chartMap_mul`: passing to the smaller chart `D₊(t g)` does not change the
  chart map. This uses Mathlib's `Proj.SpecMap_awayMap_awayι` and `awayLift_comp_awayMap`.
- `chartMap_eq`: the chart map does not depend on the chart: if `e t` and `e t'` are both
  units, the maps through `D₊(t)` and `D₊(t')` agree, since both equal the map through
  `D₊(t t')`.
- `awayLift_eq_of_chartMap_eq`: a chart map determines `awayLift`. The proof cancels the
  monomorphism `Proj.awayι` and compares the induced maps on global sections, using
  `toSpecΓ_appTop` and `ΓSpecIso_naturality`.
- `chartMap_toSpecZero`: composed with `Proj.toSpecZero 𝒜 : Proj A ⟶ Spec A₀`, the chart map
  is `T.toSpecΓ ≫ Spec.map (awayLift ∘ (A₀ → A_(t)))` (Mathlib's `Proj.awayι_toSpecZero`).
- `chartMap_preimage_basicOpen`: for homogeneous `t'` of positive degree, the preimage of
  `D₊(t')` under the chart map is the basic open `T.basicOpen (e t')`. The proof combines
  Mathlib's `Proj.awayι_preimage_basicOpen`, `SpecMap_preimage_basicOpen` and
  `Scheme.toSpecΓ_preimage_basicOpen`, and removes the unit factor `(e t)⁻¹ ^ d'`.
