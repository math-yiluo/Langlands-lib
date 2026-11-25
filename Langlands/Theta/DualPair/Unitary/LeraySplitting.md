# The Leray splitting of `U(ν, ν)` in the metaplectic group of pairs

**GKT §11.2** (Corollary 11.7, p. 325; Definition 11.13, p. 330), **§12.4** (Proposition 12.27 (1),
p. 372; Proposition 12.29, p. 375), **Definition 13.15** and **Proposition 13.16** (p. 399), in
Case `3₊` with `W` split, on the metaplectic group of pairs of **§2.1** (relation (2.2), p. 47;
`Mp(𝕎)^{ℂ¹}`, p. 49) and with the book's form `⟪,⟫ = tr_{E/F}(⟨,⟩ \overline{(,)})` on `𝕎 = W ⊗ V`
(Theorem 10.28, p. 288; §11.1.1, p. 306).

The module `Langlands.Theta.DualPair.Unitary.LeraySplitting` identifies the Weil representation of
`U(ν, ν)` built in `Langlands.Theta.DualPair.Unitary.Splitting` as `ω_ψ ∘ s` for a splitting `s` of
`U(ν, ν)` in `MetaplecticGroup` (GKT Definition 13.15), proves that the scalar at the Weyl element
and the representation are unique, and defines them: `lerayScalar` and `lerayWeil`, the Weil
representation of the Leray splitting `s^V_{ψ,χ}` with data `(χ, ψ)` (Definition 11.13) in the
book's normalization.

## Content

Hypotheses of the main theorems, as in `Splitting`: `F` a nonarchimedean local field of
characteristic zero with `⅟2`; `E / F` quadratic with the module topology,
`hE : IsQuadraticInvolution c δ`; `Q` Hermitian (`hQ`) and invertible (`hQu`);
`ψ : UnitaryAdditiveCharacter F`; `χ : Eˣ →* Circle` continuous (`hχ`) with `hres`
(`χ|_{Fˣ} = χ_{E/F}^{|α|}`, the condition (11.2)).

**The book's form.** The Library's form `hermitianSymplecticForm` (and the pairing
`hermitianPairing`) is half of the book's.

- `hermitianTracePairing c Q = 2 · hermitianPairing c Q`, `(x, y) ↦ tr_{E/F} tr(Qᵀ x c(y)ᵀ)`
  (`hermitianTracePairing_apply`): the book's pairing of `𝕏^* = M_{α×ν}(E)` with `𝕏`; its polarized
  form is the book's `⟪,⟫` on `𝕎 = M_{α×ν}(E)²`.
- `hermitianTraceSchrodinger c ν Q ψ`: the Schrödinger model `S(𝕏^*)` of the Heisenberg group of
  `(𝕎, ⟪,⟫)` with central character `ψ` (GKT §12.4.1).
- `hermitianSchrodinger_scale_comp`: the Library's model `hermitianSchrodinger c ν Q (ψ(2 ·))`,
  composed with `traceHeisenbergEquiv` (`(w, t) ↦ (w, t/2)`), is the book's model for `ψ`. So the
  book's `ψ` is the Library's `ψ(2 ·)` read through `½`; equivalently, the Library's model for `ψ` is
  the book's model for `ψ_{1/2} : x ↦ ψ(x/2)` (from `HeisenbergGroup.schrodingerSB_comp_mulCenEquiv`
  with `a = 2`).

**The splitting (`ω = ω_ψ ∘ s`).**

- `UnitaryGroup.toIsometry hc hQ`, `UnitaryGroup.toTraceIsometry hc hQ`: `g ↦ (w ↦ w g⁻¹)`, the map
  `G(W) → Sp(𝕎)`, `g ↦ g ⊗ 1_V`, into the isometry groups of the Library's and the book's form;
  `UnitaryGroup.heisenbergAction_eq`: the action on the Heisenberg group used in `Splitting` is the
  action of `toIsometry`.
- `IsLerayWeil.splitting h hE hQ hQu hχ hres : MetaplecticGroup.Splitting (hermitianSchrodinger c ν Q ψ)
  (UnitaryGroup.toIsometry hE.involutive hQ)`, `g ↦ (w ↦ w g⁻¹, ω g)`, for a representation with
  `IsLerayWeil c ψ.complex χ Q μ κ ω`; `IsLerayWeil.weil_splitting`: its Weil representation is `ω`.
  The relation (2.2) is `IsLerayWeil.normalizes`, so the splitting is
  `MetaplecticGroup.Splitting.ofNormalizes`.
- `IsLerayWeil.splitting_mem_unitary`: it lands in `Mp(𝕎)^{ℂ¹}`, the pairs whose operator preserves
  the `L²` inner product `schwartzBruhatInner μ'` of any Haar measure `μ'`
  (`Langlands.Theta.Heisenberg.SchrodingerUnitary`).

**Uniqueness of `κ` and of `ω`.**

- `IsLerayWeil.ne_zero`: `κ ≠ 0`: the operator `κ ℱ` of the Weyl element is invertible and there is
  a non-zero Schwartz–Bruhat function (`exists_schwartzBruhat_ne_zero`).
- `IsLerayWeil.unique`: two representations `IsLerayWeil` for the same data and the same measure have
  the same scalar and are equal. In `U(ν, ν)`, `w n(1) w = p₀ w n(−1)` with `p₀` in the Siegel
  parabolic (the big-cell relation of `Splitting`); applying both representations to a function
  `φ` gives `κ² X = κ Y` and `κ'² X = κ' Y` with `X = ℱ T(n(1)) ℱ φ` and `Y = T(p₀) ℱ T(n(−1)) φ`
  independent of the scalar, and `X ≠ 0` for a suitable `φ`; so `κ = κ'`, and the two
  representations agree on the Siegel parabolic and at the Weyl element, which generate
  (`UnitaryGroup.eq_top_of_siegelParabolic_le_of_weylElement_mem`).

**`lerayScalar` and `lerayWeil`.**

- `lerayScalar c ψ χ Q μ : ℂ` and `lerayWeil c ν ψ χ Q : Representation ℂ U(ν, ν) S(M_{α×ν}(E))`
  for the book's character `ψ`: the scalar and the representation of `IsLerayWeil` for the
  Library's character `ψ(2 ·)` (defined by choice; `lerayWeil` does not depend on a measure).
- `isLerayWeil_lerayWeil`: `IsLerayWeil c (ψ(2 ·)).complex χ Q μ (lerayScalar c ψ χ Q μ)
  (lerayWeil c ν ψ χ Q)` for every Haar measure `μ` (from `exists_isLerayWeil`).
- `IsLerayWeil.eq_leray`: a representation `IsLerayWeil` for `ψ(2 ·)` has scalar `lerayScalar` and
  is `lerayWeil`; `IsLerayWeil.eq_leray'`: one for a Library character `ψ'` is `lerayWeil` for the
  book's `ψ'_{1/2}`. Independence of the measure: `IsLerayWeil.of_smul_measure` (the measure `r μ`
  multiplies the Fourier transform by `r`) and the uniqueness of Haar measure
  (`MeasureTheory.Measure.isAddLeftInvariant_eq_smul`).
- `lerayWeil_normalizes`: `ω(g) ρ(w, t) = ρ(w g⁻¹, t) ω(g)` for the book's model `ρ`;
  `leraySplitting hE hQ hQu hχ hres : MetaplecticGroup.Splitting (hermitianTraceSchrodinger c ν Q ψ)
  (UnitaryGroup.toTraceIsometry hE.involutive hQ)`, **the Leray splitting `s^V_{ψ,χ}`** of
  Corollary 11.7 / Definition 11.13; `weil_leraySplitting`: `ω_{ψ,χ} = ω_ψ ∘ s^V_{ψ,χ}` is
  `lerayWeil`; `leraySplitting_mem_unitary`: it lands in `Mp(𝕎)^{ℂ¹}`.
- The formulas of Proposition 12.27 (1) in the book's normalization:
  `lerayWeil_apply_of_mem_siegelParabolic` (for `p = [[A, B], [0, D]]`:
  `ω(p) φ(x) = s(det A) ψ(½ ⟪x A, x B⟫) φ(x A)`, `s = splittingScalar F χ |α|`),
  `lerayWeil_weylElement_apply` (`ω(w) φ(x) = lerayScalar c ψ χ Q μ · ∫ ψ(⟪x, y⟫) φ(y) dμ(y)`),
  `lerayWeil_siegelLevi_apply` (`diag(a, c(a)⁻ᵀ)` acts by `χ(det a) |N det a|^{|α|/2} φ(· a)`,
  Proposition 12.29 on the Levi); `isSmooth_lerayWeil` (Proposition 13.16);
  `lerayWeil_lintegral_enorm_sq` (unitarity for every Haar measure).

The value of `lerayScalar` (the book's `β(w) = γ(ψ_{1/2} ∘ Res_{E/F} V)^{|ν|}`, Proposition 12.29,
times the factor `C(μ)^{-1/2}` correcting the measure) is in
`Langlands/Theta/DualPair/Unitary/LerayScalar.lean` (`lerayScalar_eq`,
`lerayScalar_selfDualMeasure`). What is not here: the comparison of the Library's `χ` with the
book's (whether the Library's `χ(det a)` on `diag(a, c(a)⁻ᵀ)` is the book's `χ(det a)` on `m(a)` or
its inverse) and of the Library's Weyl element and Fourier kernel with the book's need the book's
operators `r(g)`, which are not formalized.

## Declarations

- `Langlands.Theta.hermitianTracePairing`, `hermitianTracePairing_eq_mul`,
  `hermitianTracePairing_apply`, `continuous_hermitianTracePairing_left`, `twoUnit`, `coe_twoUnit`,
  `hermitianTraceSchrodinger`, `hermitianTraceSchrodinger_apply`, `traceHeisenbergEquiv`,
  `hermitianSchrodinger_scale_comp`, `normalizes_hermitianTraceSchrodinger`.
- `Langlands.UnitaryGroup.toIsometry`, `toIsometry_apply`, `heisenbergAction_eq`, `toTraceIsometry`,
  `toTraceIsometry_apply`.
- `Langlands.Theta.IsLerayWeil.splitting`, `IsLerayWeil.weil_splitting`,
  `IsLerayWeil.splitting_mem_unitary`, `exists_schwartzBruhat_ne_zero`, `IsLerayWeil.ne_zero`,
  `IsLerayWeil.unique`.
- `Langlands.Theta.lerayScalar`, `IsLerayWeilBorel`, `lerayWeil`, `IsLerayWeil.of_smul_measure`,
  `IsLerayWeil.eq_leray`, `IsLerayWeil.eq_leray'`, `isLerayWeil_lerayWeil`, `lerayWeil_normalizes`,
  `leraySplitting`, `weil_leraySplitting`, `leraySplitting_mem_unitary`, `isSmooth_lerayWeil`,
  `lerayWeil_lintegral_enorm_sq`, `lerayWeil_apply_of_mem_siegelParabolic`,
  `lerayWeil_weylElement_apply`, `lerayWeil_siegelLevi_apply`.

## Dependencies

`Langlands.Theta.DualPair.Unitary.Splitting`, `Langlands.Theta.Metaplectic.Exact` (and through it
`Langlands.Theta.Metaplectic.Defs`), `Langlands.Theta.Heisenberg.SchrodingerUnitary`,
`Langlands.HarmonicAnalysis.CharacterTransport`.
