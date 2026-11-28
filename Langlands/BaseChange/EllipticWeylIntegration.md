# Weyl integration on the regular elliptic set of `GL_n` modulo the center

Lean module: `Langlands.BaseChange.EllipticWeylIntegration`. The theorem

`ellipticWeylIntegration : EllipticWeylIntegrationStatement.{u}`

proves the statement of `Langlands.BaseChange.EllipticWeylIntegrationStatement`. Let `F` be a
nonarchimedean local field of characteristic zero, `n > 0`, `G = GL_n(F)`, `Z` its center,
`E ⊆ G ⧸ Z` the image of the regular elliptic set, and `D` the determinant window
`0 ≤ ord_F(det g) < n` of `Langlands.BaseChange.CentralQuotientWindowMeasure`. The theorem
constructs one measure `ν` on `G ⧸ Z` with `ν(Eᶜ) = 0`, before any Haar measure `μ` is given.
For every Haar measure `μ` on `G ⧸ Z` and every `Φ` integrable on `E`, the orbital integrals
`x ↦ ∫ Φ(g x g⁻¹) dμ(g)` are defined `ν`-almost everywhere and `ν`-integrable, and they integrate
to `∫_E Φ dμ`.

## The measure

Tori are the elements of `WeylTorus F n`, the centralizers of regular semisimple elements. For a
torus `T` with a Haar measure `μT`:

- `WeylTorus.ellipticWindowPoints T` is the set of regular points `t` of `T` that are regular
  elliptic and lie in `D`. It is open (`regularEllipticOpen`,
  `isOpen_degreeWindow_determinantOrder`), hence measurable
  (`WeylTorus.measurableSet_ellipticWindowPoints`).
- `WeylTorus.ellipticOrbitMeasure T μT` is the image in `G ⧸ Z`, under `t ↦ tZ`, of the
  restriction of `μT` to these points with density `|D(t)|` (`WeylTorus.discriminantWeight`),
  multiplied by `|W(G, T)(F)|⁻¹ · κ_T⁻¹`. Here `κ_T = subgroupWindowVolume T μT = μT(T ∩ D)`.

The measure of the theorem is `ν = ∑_{T ∈ S} ellipticOrbitMeasure T (μT T)`. The set `S` contains
one torus from each rational conjugacy class (`WeylTorus.exists_representativeSet`, through the
equivalence relation `WeylTorus.isConjugate_equivalence`). For each torus `T` the proof chooses,
from the existential result `WeylTorus.exists_haar_compatible`, a Haar measure `μT T` on `T`
that is also right invariant, together with a measure on `T \ G` compatible with a fixed Haar
measure `μG` of `G`. Only these stated properties of the chosen measures are used afterwards.
(The existence proof takes `Measure.haar` on `T`, which is right invariant because `T` is
commutative (`WeylTorus.haar_isMulRightInvariant`), and obtains the compatible measure from
Weil's existence theorem `compatibleMeasureExists`, since `T` is closed
(`WeylTorus.isClosed_subgroup`).)

Each term of `ν` is carried by `E` (`WeylTorus.ellipticOrbitMeasure_compl`), so `ν(Eᶜ) = 0`.

How this `ν` compares with the literature (the Lean does not formalize this comparison): for an
elliptic torus `T`, every regular point of `T` is regular elliptic and `Z \ T` is compact, so the
image of `μT` restricted to `T ∩ D` is `κ_T` times the Haar probability measure `dt̄` of `T ⧸ Z`.
For a torus that is not elliptic, no regular point is elliptic. Hence `ν` is Clozel's measure
`∑_T |W(G,T)|⁻¹ |D(t)| dt̄` over the elliptic tori up to conjugacy. The proof below does not use
these facts; it treats every torus of `S` alike.

## The measure identity

Let `μG = Measure.haar` on `G` and `μ₀ = windowMeasure F n μG`, the image in `G ⧸ Z` of `μG`
restricted to `D`. It is a Haar measure (`windowMeasure_isHaarMeasure`) and therefore invariant
under inversion (`centralQuotient_isInvInvariant`). Write `m(g, x) = g x g⁻¹` on `G ⧸ Z`; `m` is
continuous, hence measurable (`measurable_centralQuotientConj`).

`windowMeasure_restrict_regularElliptic_eq_map` proves that `S` is countable and

`μ₀|_E = m_*(μ₀ × ν)`.

Fix a measurable `A ⊆ G ⧸ Z`.

1. **Left side.** By `windowMeasure_apply` and `mk_preimage_image_regularElliptic` (the regular
   elliptic set is a union of cosets of `Z`, by `isRegularElliptic_center_mul`), `μ₀(A ∩ E)` is
   `μG(Y)` with `Y = mk⁻¹(A) ∩ {regular elliptic} ∩ D`. The set `Y` consists of regular semisimple
   elements. So the ordinary Weyl decomposition `ordinaryWeylMeasureDecomposition`, with the local
   pushforwards `ordinaryWeylHaarLocalPushforwards`, writes `μG(Y)` as a sum over `T ∈ S`. The
   term of `T` is `|W(G, T)(F)|⁻¹ ρ_T(orb_T⁻¹(Y))`. Here `orb_T(Tx, t) = x⁻¹ t x` is
   `WeylTorus.ordinaryOrbitMap` (measurable by `WeylTorus.measurable_ordinaryOrbitMap`), and
   `ρ_T = WeylTorus.weightedOrdinaryOrbitMeasure` is the product of the compatible measure `ν_T`
   on `T \ G` with `μT` on the regular points, with density `|D(t)|`. The decomposition also
   gives the countability of `S`.
2. **Right side.** By `Measure.prod_apply_symm`, `(μ₀ × ν)(m⁻¹(A))` is the integral over `ν` of
   `x ↦ μ₀{g : g x g⁻¹ ∈ A}`, a sum over `T ∈ S` by `lintegral_sum_measure`.
3. **One torus.** `WeylTorus.lintegral_ellipticOrbitMeasure` identifies the two terms of `T`.
   - Both sides become integrals over the regular points `t` of `T`: on the left by Tonelli for
     the product with density (`prod_withDensity_snd_apply`), on the right by unfolding the image
     of a restricted measure with density (`lintegral_smul_map_withDensity_restrict`).
   - Regular ellipticity and the window are invariant under conjugation
     (`isRegularElliptic_inv_mul_mul_iff`, from `charpoly_inv_mul_mul`, and
     `inv_mul_mul_mem_degreeWindow_iff`). So `(Tx, t)` lies in `orb_T⁻¹(Y)` exactly when `t` is an
     elliptic window point and `x⁻¹ t x ∈ A` modulo `Z`.
   - For such `t` the inner integral is `|D(t)| · ν_T(C_t)` with
     `C_t = {Tx : x⁻¹ t x Z ∈ A}`. The slice lemma `WeylTorus.windowVolume_mul_measure_slice`
     gives `κ_T · ν_T(C_t) = μ₀{g : g t g⁻¹ ∈ A}`. This is Weil's formula on the window,
     `measure_preimage_inter_window_eq` (the torus contains the center by `WeylTorus.center_le`),
     which gives `μ₀{y : y⁻¹ t y ∈ A}`, followed by the inversion invariance of `μ₀`.
   - Since `T` is the centralizer of the regular elliptic `t`
     (`WeylTorus.glCentralizer_eq_of_regularPoint`), `κ_T` is finite (`subgroupWindowVolume_lt_top`).
     It is positive (`subgroupWindowVolume_pos`), so the factor `κ_T⁻¹` in `ellipticOrbitMeasure`
     cancels it.
   - For the other regular points both integrands vanish.

## From the measure identity to the theorem

Every Haar measure `μ` on `G ⧸ Z` is `c · μ₀` with `c = haarScalarFactor μ μ₀`
(`Measure.isMulLeftInvariant_eq_smul`; `G ⧸ Z` is second countable and locally compact). The
scalar passes through restriction, the product and the image, so `μ|_E = m_*(μ × ν)`. The general
lemma `integral_fubini_of_restrict_eq_map` then applies: if `μ|_E` is the image of `μ × ν` under
a measurable `m` and `Φ` is integrable on `E`, Fubini's theorem for `Φ ∘ m` on `μ × ν`
(`Integrable.prod_left_ae`, `Integrable.integral_prod_right`, `integral_prod_symm`) gives
exactly the three conclusions of the statement.

## Auxiliary results

- `charpoly_inv_mul_mul`, `isRegularElliptic_inv_mul_mul_iff`, `determinantOrder_inv_mul_mul`,
  `inv_mul_mul_mem_degreeWindow_iff`: conjugation invariance.
- `WeylTorus.sFinite_comap_regularPoints`, `WeylTorus.sFinite_ellipticOrbitMeasure`: s-finiteness.
  The regular points form an open set (`regularSemisimpleOpenConull`), and the torus is second
  countable.
- `WeylTorus.measurable_discriminantWeight`: `|D(t)|` is locally constant on the regular points
  (`WeylTorus.isLocallyConstant_discriminantWeight`), hence measurable.

## Sources

The formula is the Weyl integration formula of Henniart–Lemaire, *Changement de base et
induction automorphe pour GL_n en caractéristique non nulle*, Mém. SMF 124 (2011), II.2.10,
formula (2), restricted to functions on `G ⧸ Z` supported on the regular elliptic set. Clozel,
*Invariant harmonic analysis on the Schwartz space of a reductive p-adic group* (1991), uses it in
this form, with the measure `ν` above, in the proof of Theorem 3. The Lean proof does not follow
a quotient-by-the-center argument. It works on `G` with the fundamental domain `D` for the
powers of the scalar uniformizer, the ordinary Weyl decomposition of Haar measure on the regular
semisimple set, and Weil's formula for `T \ G` restricted to `D`.
