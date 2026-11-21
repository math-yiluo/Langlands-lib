# Reduction of the translation stability of the orthogonal of the wave packets

Module `Langlands.Global.AdelicWavePacketTranslationReduction` reduces
`Langlands.Global.WavePacketOrthogonalTranslationStatement` (module
`Langlands.Global.AdelicWavePacketCompletenessReduction`) to two new propositions and to
`WavePacketRapidDecayStatement` of the same module. The new propositions are a convolution
stability property of wave packets and a separation lemma for right translates. It proves that
these imply `WavePacketOrthogonalTranslationStatement`. It proves neither new proposition.

| Declaration | Kind | Source |
| --- | --- | --- |
| `IsLeftFiniteTestFunction` | definition | internal (test functions for `R(φ)`) |
| `AdelicGroupPoints.rightConvolution` | definition | MW I.2.3, the action `δ(f)` by right convolution |
| `WavePacketConvolutionStatement` | statement | Arthur 2005 p.34; MW II.1.5, IV.1.7 (*), finiteness theorem of I.2.17; Bernstein–Lapid Theorem 2.3; Lapid Proposition 6 |
| `RightTranslationTestFunctionSeparationStatement` | statement | Folland 2.42, 2.51, 5.12 |
| `wavePacketOrthogonalTranslation_of_reduction` | theorem (proved) | internal |

## Sources

- C. Mœglin and J.-L. Waldspurger, *Spectral decomposition and Eisenstein series*, Cambridge
  University Press 1995, registered as `moeglin-waldspurger-1995-spectral-decomposition`:
  - I.2.3 (p.24): the action `δ` of functions on `G(𝔸)` by right convolution;
  - I.2.17 (pp.37–38): automorphic forms on `U(𝔸) M(F) \ G(𝔸)`, and "the finiteness theorem
    (see [HC] Theorem 1)": with fixed `K`-types, level and annihilating ideal of `𝔷`, these
    forms span a finite-dimensional space;
  - II.1.5 (pp.85–87): the Eisenstein series `E(λφ, π ⊗ λ)` converges normally for `g` in
    compact sets and `Re λ` in a positive cone, and is an automorphic form;
  - IV.1.3 (p.136): `A(M, π)_𝔨` is finite-dimensional; IV.1.7 (p.139): for `h ∈ ℋ_𝔨` the relation
    (*) between `E(i(π, h) φ, π)` and the action `δ(h) E(φ, π)`; IV.1.9 (a) (p.140): (*) holds
    as an equality of meromorphic functions; IV.1.11 (b) (p.141): holomorphy at `Re π = 0`.
    Chapter IV treats cuspidal data; for general `φ ∈ A^2_P` the continuation is
    Bernstein–Lapid's.
- J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein series*,
  J. Amer. Math. Soc. 37 (2024) 187–234, registered as
  `bernstein-lapid-2024-meromorphic-continuation-eisenstein`: Theorem 2.3 (p.191), published in
  the Library as `EisensteinMeromorphicContinuationStatement`
  (`Langlands.Global.AdelicEisensteinContinuationStatement`), with values in a Fréchet space of
  functions of uniform moderate growth.
- E. Lapid, *On Arthur's asymptotic inner product formula of truncated Eisenstein series*,
  Clay Math. Proc. 13 (2011), registered as
  `lapid-2011-asymptotic-inner-product-truncated-eisenstein`: Proposition 6 (p.329, PDF p.338),
  holomorphy of `E(φ, λ)` on `i𝔞_P^*` for `φ ∈ A^2_P`, published in the Library as
  `EisensteinImaginaryAxisHolomorphyStatement`
  (`Langlands.Global.AdelicEisensteinImaginaryHolomorphyStatement`).
- J. Arthur, *An introduction to the trace formula*, in *Harmonic Analysis, the Trace Formula,
  and Shimura Varieties*, Clay Math. Proc. 4 (2005), registered as
  `arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`: §7, printed p.34 (PDF p.46): the
  induced representation `I_P(λ, y)` and the identity `E(x, I_P(λ, y)φ, λ) = E(xy, φ, λ)`,
  which "follows formally from the definitions" where the series converge; the `K`-finite,
  `Z_∞`-finite vectors `H⁰_P`, dense in `H_P`.
- The Library's `EisensteinAbsoluteConvergenceStatement`
  (`Langlands.Global.AdelicEisensteinConvergenceStatement`; MW II.1.5): absolute and locally
  uniform convergence of `hK.eisensteinSeries φ λ` for sufficiently regular `λ`.
- G. B. Folland, *A Course in Abstract Harmonic Analysis*, 2nd ed., CRC Press 2015, registered as
  `folland-2015-abstract-harmonic-analysis-second`: Proposition 2.42 (continuity of translation
  in `L^p`); Theorem 2.51 with (2.52) (invariant measures on homogeneous spaces: a
  `G(𝔸)`-invariant measure on `G(F) \ G(𝔸)` exists since `G(𝔸)` and the discrete `G(F)` are
  unimodular); Theorem 5.12 (Peter–Weyl, p.143: matrix coefficients are uniformly dense in
  `C(K_∞)`).

## Definitions

Notation: `K_∞ = K.comap (ofInfinite F G)` is the archimedean part of `K`, a compact subgroup
of `G(F_∞)`.

### `IsLeftFiniteTestFunction F G Kinf φ`

`φ : G(𝔸) → ℂ` is continuous and compactly supported, the left translates
`h ↦ φ(ofInfinite k * h)`, `k ∈ Kinf`, span a finite-dimensional space, and there is an open
subgroup `L` of `G(𝔸_f)` with `φ(ofFinite l * h) = φ(h)` for `l ∈ L`.

Provenance (internal). These are the functions by which wave packets are convolved below. Left
`K_∞`-finiteness makes `I(λ, φ) v` right `K_∞`-finite: the right translate of `I(λ, φ) v` by
`k` is `I(λ, φ(k⁻¹ ·)) v`. Left `L`-invariance makes it right `L`-invariant. MW's algebra
`ℋ_𝔨` (IV.1.1) consists of smooth functions finite on both sides; here neither smoothness nor
right finiteness is required.

### `AdelicGroupPoints.rightConvolution F G φ Θ`

`R(φ)Θ(x) = ∫_{G(𝔸)} φ(h) Θ(x h) dh` for `Measure.haar` on `G(𝔸)`. This is MW's `δ(φ)Θ`
(I.2.3). The normalization of the Haar measure only multiplies `R(φ)Θ` by a positive
constant.

## Statements

`WavePacketConvolutionStatement` carries the hypotheses of `WavePacketCompletenessStatement`
unchanged. `RightTranslationTestFunctionSeparationStatement` keeps only `F`, `G` (affine,
locally of finite type, connected reductive), `K` maximal compact and the measure `μG`.
"Orthogonal" means the target's pairing `∫ y, f y * conj (Θ y.out) ∂μG = 0`.

### `WavePacketConvolutionStatement`

For every `Θ` with `IsWavePacket F G K rho hsmooth hcalc Θ`:

1. `Θ` is left `G(F)`-invariant (`IsLeftInvariantUnder F G (rationalSubgroup F G) Θ`);
2. for every `φ` with `IsLeftFiniteTestFunction F G K_∞ φ`, the function `R(φ)Θ` is again a
   wave packet: `IsWavePacket F G K rho hsmooth hcalc (AdelicGroupPoints.rightConvolution F G φ Θ)`.

The new wave packet may use different data (`k`, `v`, `c`, `E`, `D`) for the same parabolic.

Provenance (derived). Delorme does not state this. It is a standard consequence of the
`G(𝔸)`-equivariance of Eisenstein series. Bare right translates of a wave packet are in general
not wave packets of the same form: translation changes the inducing data by the `λ`-dependent
operators `I_P(λ, h)`, and by archimedean `h` it destroys `K_∞`-finiteness. Convolution with a
left `K_∞`-finite test function keeps the form, with the `λ`-dependence absorbed in entire
coefficients. This route uses the Eisenstein series of one parabolic at a time. It needs neither
the unitarity of the intertwining operators nor the isometry of Delorme's Theorem 6.1, unlike
the derivation sketched in the Markdown of `AdelicWavePacketCompletenessReduction`. The intended
proof follows.

- Identification of `E j`. `IsMeromorphicInCoordinatesOn` asks for a dense open domain of
  holomorphy `D` and local quotients `h/g` on connected neighbourhoods of every point of `ℂⁿ`.
  Two such functions that agree on a nonempty open set therefore agree on the whole common
  domain of holomorphy: the identity theorem propagates through the local quotients. Hence
  `E j λ g` equals the meromorphic continuation of `E(v j, λ)(g)` (Bernstein–Lapid) for `λ` in
  `D` and outside its polar set. It equals it on all of `i𝔞_P^*`, where both are holomorphic
  (Lapid, Proposition 6).
- Part 1. `E(v, λ)(γ g) = E(v, λ)(g)` for `γ ∈ G(F)` and regular `λ` (MW II.1.5). Comparing
  `λ ↦ E j λ (γ g)` with `λ ↦ E j λ g` by the identity theorem as above gives the same equality
  for `λ ∈ D ⊇ i𝔞_P^*`. So the integrands defining `Θ(γ g)` and `Θ(g)` coincide.
- Part 2. With the Library's normalization
  `E(v, λ)(x) = ∑_{δ ∈ P(F) \ G(F)} v(δx) exp⟨λ, H_P(δx)⟩` (Lapid §2), right translation acts on
  the inducing data through the `λ`-dependent operators
  `(I_P(λ, h) v)(x) = v(xh) exp⟨λ, H_P(xh) − H_P(x)⟩`: `R(h) E(v, λ) = E(I_P(λ, h) v, λ)` where
  the series converges (Arthur p.34, in his normalization). The exponential factor cannot be
  dropped, even for `P = G` (compare step 1 of the translation correspondence in the Markdown of
  `AdelicWavePacketCompletenessReduction`). Put `I(λ, φ) v = ∫ φ(h) I_P(λ, h) v dh`, that is
  `(I(λ, φ) v)(g) = e^{-⟨λ, H_P(g)⟩} ∫ φ(h) v(g h) e^{⟨λ, H_P(g h)⟩} dh` (compare MW IV.1.7 (*)).
  For regular `λ` the convergence is absolute and uniform for `h` in the compact support of `φ`
  (`EisensteinAbsoluteConvergenceStatement`), so integrating against `φ` gives
  `R(φ) E(v, λ) = E(I(λ, φ) v, λ)`.
  To see that `I(λ, φ) v j` lies in `A^2_P` (`IsSquareIntegrableInducedForm`), first note that
  the difference `H_P(xh) − H_P(x)` is invariant under left `P(𝔸)` because
  `H_P(p x) = H_P(p) + H_P(x)` for `p ∈ P(𝔸)`. Thus the left `M(F) U(𝔸)`-invariance and the
  `A_P`-equivariance of `v j` are preserved. The same difference is bounded uniformly in `x`
  and `h ∈ supp φ`: for `x = p k` it is `H_P(k h)`, and `K · supp φ` is compact. The pointwise
  absolute value of `I_P(λ, h) v` is therefore bounded by a constant times that of
  `I_P(0, h) v`, uniformly in `h ∈ supp φ` for fixed `λ`. The latter has the same inducing
  Hilbert norm as `v` by unitarity of the untwisted normalized induction (Arthur §7; the
  half-modulus is included in `v`). Minkowski's inequality now gives square integrability
  for `I(λ, φ) v`. The same bound for the twist and the height bound for `x h`, uniform on
  `supp φ`, give moderate growth from that of `v` (see the clamped norm comparison below).
  All `I(λ, φ) v j` lie in one finite-dimensional space `V ⊂ A^2_P`, independent of `λ`. Their
  `K_∞`-types lie among those of the left translates of `φ`, since
  `R(k) I(λ, φ) v = I(λ, φ(k⁻¹ ·)) v` for `k ∈ K` (`H_P(x k) = H_P(x)`). For the same reason
  they are right invariant under the open subgroup `L ∩ K_f` of `G(𝔸_f)`. Their archimedean
  smoothness uses that of `v j` and the Iwasawa logarithm, not smoothness of `φ`:
  `x e^{tX} h = x h e^{t Ad(h⁻¹) X}`, so derivatives in `x` pass under the compactly supported
  integral. They are annihilated by the common ideal of `𝔷` annihilating
  all `v j`: on `U(𝔸)`-invariant functions, `𝔷` acts through the left differential action of
  `𝔷_M` (MW I.2.17), which commutes with `I_P(λ, h)` by the left `M(𝔸)`-invariance of the
  twist. The finiteness theorem (MW I.2.17; compare IV.1.3) bounds the dimension with these
  common types, level and ideal. Take `V` to be the span of the `I(λ, φ) v j` as `λ` and `j`
  vary. In a basis `w_i` of `V`, write `I(λ, φ) v j = ∑_i b_{j i}(λ) w_i`. For each point `x`,
  `I(λ, φ) v j (x)` is entire in `λ` by the compact support of `φ`. Point evaluations span the
  dual of the finite-dimensional function space `V`, so the coefficients `b_{j i}` are entire.
  Let `E'_i` be the meromorphic continuation of `E(w_i, λ)` given by
  `EisensteinMeromorphicContinuationStatement` and `EisensteinImaginaryAxisHolomorphyStatement`.
  Both sides of `R(φ)(E j λ) = ∑_i b_{j i}(λ) E'_i λ` are meromorphic in `λ`: the Fréchet-valued
  meromorphy lets one integrate against the compactly supported `φ`. Both sides agree for regular
  `λ`, so they agree on `i𝔞_P^*`. Fubini's theorem, justified by joint continuity of the
  continued series on `i𝔞_P^* × G(𝔸)` and compact supports in both integrals, gives
  `R(φ)Θ(x) = ∫ ∑_i c'_i(y) E'_i(i e(y))(x) dy` with
  `c'_i(y) = ∑_j c j y · b_{j i}(i e(y))`. These coefficients are smooth and compactly
  supported, so `R(φ)Θ` satisfies `IsWavePacket` with the data `(w_i, c'_i, E'_i, D')`. The
  `λ`-dependence of `I(λ, φ)` is carried by the entire coefficients `b_{j i}`.
- Parabolics and compact subgroups. `IsWavePacket` ranges, like the target, over every presented
  parabolic `P` with `P(𝔸)K = G(𝔸)`, not only over those containing `P₀` (see "Non-standard
  parabolics" in the Markdown of `AdelicWavePacketCompletenessReduction`). The argument above
  treats every such `P` directly, with the given `K`. The Library statements it uses
  (`EisensteinAbsoluteConvergenceStatement`, `EisensteinMeromorphicContinuationStatement`,
  `EisensteinImaginaryAxisHolomorphyStatement`) are stated for every presented parabolic `P`
  and every maximal compact `K` with `IsIwasawaCompact p K`; their Markdown reduces them to the
  sources' case of `K` in good position ("The compact subgroup" in
  `AdelicEisensteinConvergenceStatement.md`). The identity `R(h) E(v, λ) = E(I_P(λ, h) v, λ)`
  uses only the definition of the series and `H_P(x k) = H_P(x)` for `k ∈ K`. The finiteness
  theorem, stated in MW I.2.17 for parabolics containing a fixed minimal one and `K` in good
  position, transfers. Take `γ ∈ G(F)` with `γ P γ⁻¹ ⊇ P₀` (step 1 of "Non-standard
  parabolics") and `n ∈ G(F_∞)` with `K_{0,∞} = n K_∞ n⁻¹` for a maximal compact `K₀` in good
  position with respect to `P₀`. Then `ψ ↦ ψ(γ⁻¹ · n)` maps the functions on
  `U(𝔸) M(F) \ G(𝔸)` with given right `K_∞`-types, level and annihilating ideal of `𝔷`
  bijectively onto the functions on `U'(𝔸) M'(F) \ G(𝔸)`, `P' = γ P γ⁻¹`, with the
  corresponding `K_{0,∞}`-types, the same level and the same ideal (`𝔷` is `Ad`-invariant). It
  preserves moderate growth. For `N > 0`, `HasModerateGrowthFunction` (a bound
  `C ‖x‖_ρ^r` with the raw height and real `r`) is equivalent to a bound by a nonnegative power
  of the clamped norm `max(1, ‖x‖_ρ)`, because
  `N^{-[F:ℚ]} max(1, ‖x‖_ρ) ≤ ‖x‖_ρ ≤ max(1, ‖x‖_ρ)` (`one_le_adelicHeight`). The clamped
  norm of `γ⁻¹ x n` is at most a constant times that of `x` by its submultiplicativity (step 4
  of "Non-standard parabolics"). The case
  `N = 0`, which `EisensteinMeromorphicContinuationStatement` excludes, is trivial: the
  hypothesis `IsClosedSubgroup rho` makes `rho` a closed immersion into `GL_0`, which forces `G`
  to be trivial, so `R(φ)` multiplies every function by the constant `∫ φ`.

### `RightTranslationTestFunctionSeparationStatement`

Let `f ∈ L²([G], μG)` and let `Θ : G(𝔸) → ℂ` be left `G(F)`-invariant with
`y ↦ Θ(y.out)` in `L²([G], μG)`. Suppose `∫ y, f y · conj (R(φ)Θ (y.out)) ∂μG = 0` for every
`φ` with `IsLeftFiniteTestFunction F G K_∞ φ`. Then for every `g ∈ G(𝔸)`,
`∫ y, f(y g) · conj Θ(y.out) ∂μG = 0`, where `y g` is
`LeftCosetSpace.rightTranslate (rationalSubgroup F G) g y`.

Provenance (derived). The intended proof first replaces `Θ` by a Borel function (see
"Integrals" below). This changes neither `R(φ)Θ` at any point nor the pairing with `Θ`. `μG`
is right `G(𝔸)`-invariant by `LeftCosetSpace.measurePreserving_rightTranslate_discrete`
(`Langlands.Global.LeftCosetFundamentalDomain`) and `AdelicGroupPoints.adelicHaarUnimodularity`
(`Langlands.Global.AdelicHaarUnimodularityProof`); compare Folland 2.51. Thus `‖R(h)Θ‖₂ = ‖Θ‖₂` and
`⟨f, R(h)Θ⟩ = ⟨R(h⁻¹) f, Θ⟩`. By Fubini's theorem, justified by Cauchy–Schwarz,
`⟨f, R(φ)Θ⟩ = ∫ conj φ(h) · F(h) dh` with `F(h) = ⟨R(h⁻¹) f, Θ⟩`. `F` is continuous by the
strong continuity of the right regular representation (Folland 2.42 transported to `[G]`). The
conjugates `conj φ` of the test functions are dense in `C_c(G(𝔸))` for the inductive limit
topology. Averaging over a small open compact subgroup of `G(𝔸_f)` gives left invariance.
Convolving on the left over `K_∞` with a `K_∞`-finite approximate identity, which exists by
Peter–Weyl (Folland 5.12), gives left `K_∞`-finiteness. Hence `∫ ψ F = 0` for all
`ψ ∈ C_c(G(𝔸))`, so `F = 0`, that is `⟨R(g) f, Θ⟩ = 0` for every `g`.

### Integrals

All integrals are Bochner integrals, which are `0` for non-integrable integrands. In
`RightTranslationTestFunctionSeparationStatement`, the pairings `f · conj (R(φ)Θ)` and
`f(· g) · conj Θ` are integrable for `f, Θ ∈ L²`.

Measurability. `MemLp` gives `θ(y) = Θ(y.out)` only almost-everywhere strong measurability,
not measurability. Left `G(F)`-invariance gives `Θ = θ ∘ π` for the quotient map `π`. Choose a
Borel `θ₀` with `θ = θ₀` outside a `μG`-null set `Z`. `μG` is the quotient of Haar measure by
`LeftCosetSpace.discreteQuotientMeasure`, which satisfies `QuotientMeasureEqMeasurePreimage`
(`discreteQuotientMeasure_compatible`) and `G(F)` is countable. So `π⁻¹(Z)` is Haar-null, and
`Θ = θ₀ ∘ π` almost everywhere on `G(𝔸)`. Left translation preserves Haar-null sets, so
`h ↦ Θ(x h)` and `h ↦ θ₀(π(x h))` agree almost everywhere for every `x`. Hence
`R(φ)Θ(x) = R(φ)(θ₀ ∘ π)(x)` for every `x`. All pairings depend only on almost-everywhere
classes on `[G]`. So the proof may assume `Θ = θ₀ ∘ π` with `θ₀` Borel, and Fubini's theorem
then applies to `(y, h) ↦ φ(h) θ₀(y h)` on `[G] × G(𝔸)`. A left `G(F)`-invariant `Θ` that is
square integrable on `[G]` is locally integrable on `G(𝔸)`: for compact `C`, folding gives
`∫_C |Θ| = ∫_{[G]} |θ| N_C dμG`, where `N_C(y) = #{γ ∈ G(F) : γ y.out ∈ C}` is bounded and
supported on the compact image of `C`. So `R(φ)Θ(x)` is an absolutely convergent integral for
every `x`, and `‖R(φ)Θ‖₂ ≤ ‖φ‖₁ ‖Θ‖₂` by Minkowski's inequality. In
`WavePacketConvolutionStatement`, `R(φ)Θ(x)` is the integral of a continuous compactly
supported function, since a wave packet is continuous: by the identification of the `E j`
above, the integrand is jointly continuous on `i𝔞_P^* × G(𝔸)`. So no hypothesis holds only
through the value `0` of a divergent integral.

## The reduction theorem

`wavePacketOrthogonalTranslation_of_reduction (hA : WavePacketConvolutionStatement)
(hB : RightTranslationTestFunctionSeparationStatement) (hS : WavePacketRapidDecayStatement) :
WavePacketOrthogonalTranslationStatement`.

Proof (as implemented). Introduce the data of the target, `f ∈ L²([G])` orthogonal to every
wave packet, `g ∈ G(𝔸)` and a wave packet `Θ`.

1. `hA` gives that `Θ` is left `G(F)`-invariant and that `R(φ)Θ` is a wave packet for every
   test function `φ`.
2. `hS` with `m = 0` gives `y ↦ Θ(y.out) · σ_{[G]}(y)^0` in `L²`. `simpa` rewrites this to
   `y ↦ Θ(y.out)` in `L²`.
3. The orthogonality hypothesis, applied to the wave packets `R(φ)Θ`, gives `f ⊥ R(φ)Θ` for
   every test function `φ`. `hB` then gives `f(· g) ⊥ Θ`.

The theorem uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Scope

Neither new statement is proved here. Their expected inputs: for
`WavePacketConvolutionStatement`, the Library's Eisenstein series, its continuation and
imaginary-axis holomorphy statements, the finiteness theorem for automorphic forms and an
identity theorem for `IsMeromorphicInCoordinatesOn`, which the Library does not have yet; for
`RightTranslationTestFunctionSeparationStatement`, the published right-invariance results
above, strong continuity of quotient translation on `L²`, Fubini's theorem and Peter–Weyl for
`K_∞`.
