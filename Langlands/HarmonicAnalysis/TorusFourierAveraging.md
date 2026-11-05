# Averaging over a torus of twists: the first bound in the proof of Waldspurger's Prop. VI.3.1

Lean module: `Langlands.HarmonicAnalysis.TorusFourierAveraging`, namespace
`Langlands.HarmonicAnalysis.TorusFourier`. It imports
`Langlands.HarmonicAnalysis.TorusFourierDecay`: `torusCharacter` (`z ↦ ∏ⱼ zⱼ^{nⱼ}` on
`J → Circle`), `continuous_torusCharacter`, `torusFourierCoeff`
(`∫ f(z) torusCharacter n z dν(z)`), `torusPartialDeriv` and the decay estimate
`norm_torusFourierCoeff_le_rpow`; through it, `IsSmoothFiniteTorusFunction` from
`Langlands.Representation.Plancherel.RationalOrbitSmoothFunctions` (read in the namespace
`Langlands.Plancherel`). From Mathlib it uses `MeasureTheory.integral_mul_left_eq_self`,
`MeasureTheory.integral_integral_swap`, `MeasureTheory.integral_const`,
`MeasureTheory.integral_mul_const`, `MeasureTheory.norm_integral_le_of_norm_le_const` and
`Continuous.integrable_of_hasCompactSupport`.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI
10.1017/S1474748003000082. Printed page numbers; the PDF page is the printed page minus 234.

- VI.3, printed p. 302 (PDF p. 68), proof of Prop. VI.3.1: for `ϕ ∈ C^∞(Im X(M))` and `g ∈ G`,
  "`f_{ϕ,ψ}(g) = ∫_{Im X(M)} µ(ω ⊗ χ) ϕ(χ) (E_P^G sp_χ ψ)(g) dχ`. (1)"
- Printed p. 303 (PDF p. 69): "Pour `χ ∈ Im X(M)`, `λ ∈ Im X(G)` et `g ∈ G`, on a
  `(E_P^G sp_{λχ} ψ)(g) = λ(g) (E_P^G sp_χ ψ)(g)`. Pour `g ∈ G` et `ϕ ∈ C^∞(Im X(M))`,
  définissons une fonction `ϕ_g` sur `Im X(M)` par `ϕ_g(χ) = ∫_{Im X(G)} ϕ(λχ) λ(g) dλ`. (3)
  Alors `f_{ϕ,ψ}(g) = ∫_{Im X(G)\Im X(M)} µ(ω ⊗ χ) ϕ_g(χ) (E_P^G sp_χ ψ)(g) dχ`." Then estimate
  (4), `|∫_{Im X(G)} ϕ'(λ) λ(g) dλ| ≤ (1 + (H_G(g)))^{-r} ν_G(D, ϕ')`, and: "En utilisant le
  Lemme VI.2.2, on en déduit qu'il existe `D ∈ D_M` tel que pour tout `ϕ ∈ C^∞(Im X(M))` et
  tout `g ∈ G`, on ait l'inégalité `|f_{ϕ,ψ}(g)| ≤ (1 + |H_G(g)|)^{-r} Ξ(g) ν_M(D, ϕ)`."

Here `ν_M(D, ϕ) = sup{|dϕ(χ)|; d ∈ D, χ ∈ Im X(M)}` for a finite set `D` of constant-coefficient
differential operators on `Im X(M)` (printed p. 302).

- I.1, printed p. 239 (PDF p. 5), normalization of `dλ`: "L'application de restriction
  `Im X(G) → Im X(A_G)` est surjective de noyau fini. On munit `Im X(A_G)` de la mesure de Haar
  de masse totale 1 et `Im X(G)` de la mesure pour laquelle l'application précédente préserve
  localement les mesures." So the total mass of `dλ` is
  `d_G = |ker(Im X(G) → Im X(A_G))|`, which need not be `1` (for `GL_2` the restriction is
  `z ↦ z²` in circle coordinates and `d_G = 2`).

## Scope: abstract data and coordinates

The module does not construct `Im X(M)`, `Im X(G)`, the functions `χ ↦ (E_P^G sp_χ ψ)(g)` or
`H_G`. Its data are:

- `T`, a group with a topology, `[IsTopologicalGroup T]`, a measurable structure with
  `[BorelSpace T]`, and, in the integral statements, `[CompactSpace T]` and a finite left
  invariant measure `μ` (`[IsFiniteMeasure μ] [μ.IsMulLeftInvariant]`), in place of
  `Im X(M)` with its measure;
- `J` a finite type and `ι : (J → Circle) → T` a continuous map, in place of the torus
  `Im X(G)` written in coordinates `(S¹)^J` and mapped to `Im X(M)`; no homomorphism property
  of `ι` is used;
- `ν` a finite measure on `J → Circle` (`[IsFiniteMeasure ν]`; `[IsProbabilityMeasure ν]` in
  `integral_mul_eq_integral_torusAverage_mul` and `norm_integral_mul_le_rpow`; and
  `[ν.IsMulLeftInvariant]` in the bounds) in place of Waldspurger's measure `dλ` on `Im X(G)`.
  Waldspurger's `dλ` has total mass `d_G` (I.1 above), so it is `ν` only when `ν` has mass
  `d_G`; the probability-normalized Haar measure is `d_G⁻¹ dλ`, and with it `torusAverage` is
  `d_G⁻¹` times the printed `ϕ_g`. The probability statements are therefore
  probability-normalized analogues of Waldspurger's averaging step; the mass appears explicitly
  in `integral_torusAverage_mul` and `norm_torusAverage_le_rpow`;
- `n : J → ℤ`, so that `torusCharacter n z` plays the role of `λ(g)` for `λ = ι(z)`;
  for the source `n` is the coordinate vector of `H_G(g)`;
- `φ : T → ℂ` (in the source `χ ↦ µ(ω ⊗ χ) ϕ(χ)`), and `F : T → ℂ` (in the source
  `χ ↦ (E_P^G sp_χ ψ)(g)`), with the equivariance `F(ι(z) χ) = torusCharacter n z · F(χ)`
  as an explicit hypothesis.

## Declarations

- `torusAverage ν ι φ n χ`, the main definition: `torusFourierCoeff ν (z ↦ φ(ι(z) χ)) n`,
  i.e. `∫ φ(ι(z) χ) torusCharacter n z dν(z)` (`torusAverage_apply`). With `ν` of total mass
  `d_G` this is Waldspurger's `ϕ_g(χ)` of (3) in coordinates; with a probability measure `ν` it
  is `d_G⁻¹ ϕ_g(χ)`. Only `[Group T]` is used.
- `integral_torusAverage_mul μ ν hι hφ hF hFn` (hypotheses: `CompactSpace T`, `μ` finite and left
  invariant, `ν` finite, `hι : Continuous ι`, `hφ : Continuous φ`, `hF : Continuous F`, `hFn`
  the equivariance): `∫_T φ_g(χ) F(χ) dμ = ν(J → Circle) • ∫_T φ(χ) F(χ) dμ`. For `ν` of mass
  `d_G` this is the source-normalized identity `∫_T ϕ_g F dμ = d_G ∫_T φ F dμ`.
- `integral_mul_eq_integral_torusAverage_mul μ ν hι hφ hF hFn` (the same hypotheses with `ν` a
  probability measure): `∫_T φ(χ) F(χ) dμ = ∫_T φ_g(χ) F(χ) dμ`, the probability-normalized
  form.
- `norm_torusAverage_le_rpow ν hφ hr hM0 hM n χ` (hypotheses: `[DecidableEq J]`, `ν` finite and
  left invariant, `hφ : ∀ χ, IsSmoothFiniteTorusFunction (z ↦ φ(ι(z) χ))`, `hr : r ≤ k`,
  `hM0 : ∀ χ z, |φ(ι(z) χ)| ≤ M`, `hM : ∀ χ j z, |∂ⱼ^k (z ↦ φ(ι(z) χ))(z)| ≤ M`): estimate (4)
  for `ϕ_g`, `|φ_g(χ)| ≤ 2^k (1 + |J|) (M ν(J → Circle)) (1 + ‖n‖)^{-r}`.
- `norm_integral_mul_le_rpow μ ν hι hφc hφ hF hFn hr hM0 hM hB` (the hypotheses of
  `integral_mul_eq_integral_torusAverage_mul` and `norm_torusAverage_le_rpow`, with `ν` a left
  invariant probability measure, `hφc : Continuous φ`, and `hB : ∀ χ, |F(χ)| ≤ B`): the first
  bound, `|∫_T φ F dμ| ≤ 2^k (1 + |J|) M μ(T) B (1 + ‖n‖)^{-r}`. The auxiliary measure `ν` does
  not occur in the conclusion, so the bound does not depend on the normalization of `dλ`.

For the source, `B = c Ξ(g)` is the uniform bound of Lemma VI.2.2 over the twists of `ω`
(in the Library, generically, `norm_family_coefficientMap_le_xi` in `InducedCoefficientTwistXi`,
under its own hypotheses), and `M` bounds `φ` and its `k`-th derivatives along the directions
of `Im X(G)`, which is bounded by some `ν_M(D, µ(ω ⊗ ·) ϕ)`. The resulting inequality has the
form `|f_{ϕ,ψ}(g)| ≤ C (1 + ‖n(g)‖)^{-r} Ξ(g) M` of Waldspurger's bound, with `‖n(g)‖` the
sup norm of the coordinates of `H_G(g)` in place of `|H_G(g)|`. This combination is not stated
in the module.

## Proof outline

The proof differs from Waldspurger's, who passes to the quotient `Im X(G)\Im X(M)`. For each
`z`, left invariance of `μ` gives `∫_T φ F dμ = ∫_T φ(ι(z) χ) F(ι(z) χ) dμ(χ)
= ∫_T φ(ι(z) χ) torusCharacter n z F(χ) dμ(χ)`. Integrating over `z` against the finite measure
`ν` (the left side becomes `ν(J → Circle) • ∫_T φ F dμ` by `integral_const`) and exchanging the
integrals (Fubini, `integral_integral_swap`; the integrand is continuous on the compact space
`(J → Circle) × T`) gives `∫_T φ_g F dμ`; this is `integral_torusAverage_mul`, and the
probability form follows from `ν(J → Circle) = 1`. When `ι` is a homomorphism and `ν` is
invariant, `φ_g F` is invariant under `ι(J → Circle)`, so the integral over `T` corresponds to
Waldspurger's integral over the quotient. Taking on `Im X(G)\Im X(M)` the quotient measure
determined by `dχ` and `dλ` (of mass `d_G`), so that
`∫_{Im X(M)} = ∫_{Im X(G)\Im X(M)} ∫_{Im X(G)} dλ`, one gets `∫_{Im X(G)\Im X(M)} ϕ_g F = d_G⁻¹ ∫_{Im X(M)} ϕ_g F = ∫_{Im X(M)} φ F`, consistent with
`integral_torusAverage_mul` for `ν` of mass `d_G`. This quotient comparison is an explanation
and is not formalized. The bound then follows from `norm_torusAverage_le_rpow` (a direct
application of `norm_torusFourierCoeff_le_rpow`) with `ν(J → Circle) = 1`, and
`norm_integral_le_of_norm_le_const`.

## Not covered

- The actual groups `Im X(M)`, `Im X(G)`, the coordinates of `H_G(g)` and the identification of
  `M` with a seminorm `ν_M(D, ·)`.
- The actual measure `dλ` of I.1 and its mass `d_G`; the module only records the mass of an
  abstract `ν` (in the Library, the scaling for the actual characters is
  `rationalUnitaryUnramifiedCharacterHaar_eq_smul_probability` in
  `Langlands.Representation.Plancherel.RationalCharacterHaar`, which is not used here).
- The remaining steps of the proof of Prop. VI.3.1 (the bounds on `n(ϕ)`, `n^w(ϕ)`, `n^+(ϕ)`
  in (2)) and Prop. VI.3.1 itself.
