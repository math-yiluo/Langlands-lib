# Lemma II.3.5: elements of small height lie in `a⁻¹ Γ a M Γ̄`

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.OpenCellLemma`, namespace
`Langlands.HarishChandraSchwartz`. It imports the published module `ConjugationBound`, whose
Prop `ConjugationSigmaBound` is inequality (2) of the proof of Proposition VIII.3.1 and a
hypothesis of `lintegral_conj_mul_le`.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI
10.1017/S1474748003000082. Printed page numbers; the PDF page is the printed page minus
234.

- Lemma II.3.5 and its proof, printed pp. 257–259 (PDF pp. 23–25). Statement: for a maximal
  standard parabolic `P = M U`, `α ∈ Δ_0` with `Δ_0^M = Δ_0 - {α}`, and compact open
  subgroups `Γ ⊆ U`, `Γ̄ ⊆ Ū`, there is `C > 0` such that for `a ∈ Ā_0^+`, `g ∈ G`,
  `1 + σ(g) + σ(a g a^{-1}) ≤ C ⟨α, H_0(a)⟩` implies `g ∈ a^{-1} Γ a M Γ̄`.
  - Step (2): with constants `C_2, …, C_5` (`log ‖τ_P(g) e_1‖ ≤ C_2 (1 + σ(g))`;
    `-C_3 ≤ log ‖τ_P(k) e_1‖` on `K`; `C_4 ⟨α, H_0(a)⟩ ≤ -⟨Re(χ_i), H_0(a)⟩` for `i ≥ 2`;
    `sup_{i ≥ 2} log |y_i| ≤ -C_5 ⇒ ū ∈ Γ̄` for `τ_P(ū) e_1 = Σ y_i e_i`) and
    `C_1 = C_4 (C_2 + C_3 + C_5)^{-1} log q`: for `g ∈ K ∩ Ū P`,
    `1 + σ(a g a^{-1}) ≤ C_1 ⟨α, H_0(a)⟩` implies `g ∈ Γ̄ P`.
  - Step (3): writing `g = k p` and using Lemma II.3.3 (constant `C_7 ≥ 1`),
    `1 + σ(g) + σ(a g a^{-1}) ≤ C_6 ⟨α, H_0(a)⟩` with `C_6 = C_1 C_7^{-1}` implies `g ∈ Γ̄ P`,
    first for `g ∈ Ū P` and then for all `g` by density of `Ū P` and closedness of `Γ̄ P`.
  - Conclusion: exchanging `P_0, P` with `P̄_0, P̄` gives `C_8`; with `C = inf(C_6, C_8)`,
    applying the two statements to `a g a^{-1}` and `g^{-1}` gives
    `g ∈ a^{-1} Γ a P̄ ∩ P Γ̄ = a^{-1} Γ a M Γ̄`.
- II.2 (1)–(5), printed pp. 253–254 (PDF pp. 19–20): the properties of `τ_P` behind the
  hypotheses of step (2); in particular (4) says `ū ↦ τ_P(ū) e_1` takes values in
  `e_1 + E'_P`, so the first coordinate of `τ_P(ū) e_1` is `1`.
- Lemma II.3.3, printed p. 256 (PDF p. 22): `1 + σ(a p a^{-1}) ≤ C (1 + σ(p))` for
  `a ∈ Ā_0^+`, `p ∈ P_0`.
- Proof of Proposition VIII.3.1, printed p. 323 (PDF p. 89): inequality (1),
  `1 + σ(a) ≤ C_1 (1 + ⟨α, H_0(a)⟩)` on `Ā_0^+(α) ∩ G^1`, and the deduction of (2),
  `1 + σ(a) ≤ C_2 (1 + σ(g) + σ(a g a^{-1}))` for `g ∈ S(a) = G - a^{-1} Γ a M Γ̄`, from
  Lemma II.3.5.

## Scope: abstract data and explicit hypotheses

`G` is a group (with a topology in step (3)), `σ, t : G → ℝ` are weights (Waldspurger's
height and `t(a) = ⟨α, H_0(a)⟩`), and `A`, `K`, `P`, `Ū`, `Γ`, `Γ̄`, `P̄` are sets or
subgroups of `G` as stated. None of the hypotheses below is proved here for Waldspurger's
data. The coordinates of `τ_P(g) e_1` enter only through their absolute values
`w(g)_i = |x_i(g)|_F`; the constant `C_4` of the Lean statement is Waldspurger's
`C_4 log q`.

## Definitions

- `OpenCellBound σ t A Ω C`: for all `a ∈ A` and `g`, `1 + σ(g) + σ(a g a^{-1}) ≤ C t(a)`
  implies `g ∈ Ω(a)` (the conclusion of Lemma II.3.5, with `Ω(a) = a^{-1} Γ a M Γ̄`).

## Results

- `mem_of_coordinate_bounds` (step (2)). Hypotheses: `C_2 > 0`, `C_3 ≥ 0`, `C_4 > 0`,
  `C_5 > 0`, `σ ≥ 0` (`hσ`); `w(g)_i ≤ exp(C_2 (1 + σ(g)))` (`h1`); for `k ∈ K` some
  `w(k)_i ≥ exp(-C_3)` (`h2`); for `a ∈ A`, all `g` and `i ≠ i_1`,
  `exp(C_4 t(a)) w(g)_i ≤ w(a g a^{-1})_i` (`h3`); for `ū ∈ Ū`, `p ∈ P` some `c > 0` with
  `w(ū p)_i = c w(ū)_i` for all `i` (`h4`, from II.2 (1)); `w(ū)_{i_1} = 1` on `Ū` (`h5`, from
  II.2 (4)); and `w(ū)_i ≤ exp(-C_5)` for all `i ≠ i_1` implies `ū ∈ Γ̄` (`h6`). Conclusion:
  there is `C_1 > 0` such that for `a ∈ A`, `ū ∈ Ū`, `p ∈ P` with `ū p ∈ K`,
  `1 + σ(a ū p a^{-1}) ≤ C_1 t(a)` implies `ū ∈ Γ̄`.
- `mem_mul_of_dense` (step (3)). Hypotheses: `σ ≥ 0`, `σ(xy) ≤ σ(x) + σ(y)`,
  `σ(x^{-1}) = σ(x)`, `σ(k g) = σ(g)` for `k ∈ K`; subgroups `P_0 ≤ P` with `G = K P_0`
  (`hiwa`); `C_7 ≥ 1` with `1 + σ(a p a^{-1}) ≤ C_7 (1 + σ(p))` for `a ∈ A`, `p ∈ P_0`
  (`h33`, Lemma II.3.3); the conclusion of step (2) with a constant `C_1` (`h2`); `Ū P` dense
  (`hdense`); `Γ̄ P` closed (`hclosed`); and, for `a ∈ A` and every `g`, `σ(g')` and
  `σ(a g' a^{-1})` equal `σ(g)` and `σ(a g a^{-1})` for `g'` near `g` (`hloc`). Conclusion:
  for `a ∈ A`, `1 + σ(g) + σ(a g a^{-1}) ≤ (C_1 / C_7) t(a)` implies `g ∈ Γ̄ P`.
- `openCellBound_of_mul` (conclusion of the lemma). Hypotheses: `σ ≥ 0`,
  `σ(x^{-1}) = σ(x)`, `C_6, C_8 > 0`; step (3) for `(P, Γ̄)` with `C_6` (`h3`); its analogue
  `1 + σ(g) + σ(a^{-1} g a) ≤ C_8 t(a) ⇒ g ∈ Γ P̄` (`h3'`); and `a g a^{-1} ∈ Γ P̄`,
  `g^{-1} ∈ Γ̄ P` imply `g ∈ Ω(a)` (`hint`, Waldspurger's
  `a^{-1} Γ a P̄ ∩ P Γ̄ = a^{-1} Γ a M Γ̄`). Conclusion:
  `OpenCellBound σ t A Ω (min C_6 C_8)`.
- `conjugationSigmaBound_of_openCellBound` (inequality (2) of the proof of VIII.3.1).
  Hypotheses: `C > 0`, `σ ≥ 0`, `T ⊆ A`, `OpenCellBound σ t A Ω C`, and inequality (1),
  `1 + σ(a) ≤ C_1 (1 + t(a))` on `T` with `C_1 ≥ 0`. Conclusion:
  `ConjugationSigmaBound σ T (a ↦ Ω(a)ᶜ)`, with constant `C_1 (1 + 1/C)`.

## Proof notes

Step (2) follows Waldspurger. With `D = C_2 + C_3 + C_5` and `C_1 = C_4 / D`, put
`s = C_1 t(a) ≥ 1 + σ(a g a^{-1}) ≥ 1`. For `i ≠ i_1`,
`w(g)_i ≤ exp(C_2 s - C_4 t(a)) = exp(-(C_3 + C_5) s) ≤ exp(-C_3 - C_5)`, so the coordinate
reaching `exp(-C_3)` is `i_1`; then `c ≥ exp(-C_3)`, and dividing by `c` gives
`w(ū)_i ≤ exp(-C_5)`. Step (3) for `g = ū p'` writes `g = k p` with `k ∈ K`, `p ∈ P_0`, so
`k = ū (p' p^{-1})`; `σ(p) = σ(g)`, `σ(a k a^{-1}) ≤ σ(a g a^{-1}) + σ(a p a^{-1})` and
Lemma II.3.3 give `1 + σ(a k a^{-1}) ≤ C_1 t(a)`, and step (2) gives `ū ∈ Γ̄`, hence
`g = ū p' ∈ Γ̄ P` directly (Waldspurger concludes through `k ∈ Γ̄ P`). A general `g` is a
limit of such elements with the same values of `σ(g)` and `σ(a g a^{-1})`, and `Γ̄ P` is
closed. The conclusion applies `h3'` to `a g a^{-1}` and `h3` to `g^{-1}`, after checking
`t(a) > 0`. For (2) of VIII.3.1, `g ∉ Ω(a)` gives `C t(a) < X = 1 + σ(g) + σ(a g a^{-1})`, so
`1 + σ(a) ≤ C_1 (1 + X/C) ≤ C_1 (1 + 1/C) X` because `X ≥ 1`.

## Open obligations

For Waldspurger's data: the representation `τ_P` with II.2 (1)–(5) and the constants of
step (2) (ledger row WSH-TAU-01, an in-book obligation of this task); the homeomorphism
property of `ū ↦ τ_P(ū) e_1` giving `h6`; the Iwasawa decomposition, Lemma II.3.3 for actual
data (a generic reduction to properties of `τ_0`, `conj_height_le_of_tau`, is in the
published module `TauEstimates`), the density of `Ū P`, the
closedness of `Γ̄ P`, the analogue for `P̄`, the identity
`a^{-1} Γ a P̄ ∩ P Γ̄ = a^{-1} Γ a M Γ̄`, and inequality (1) of VIII.3.1 are not proved here.
