# The operators `π[φ]` from the proof of Proposition III.7.1

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.SchwartzActionFamily`,
namespace `Langlands.HarishChandraSchwartz`. It imports `SchwartzActionConvolution`
(`schwartzAction_convolution`, `schwartzAction_translate_left`,
`schwartzAction_translate_right`), and through it `SchwartzAction` (`schwartzAction`,
`schwartzAction_eval`, `HasTemperedCoefficients`, `ext_smoothDual`,
`CompactOpenSubgroup.cofinal`), `Convolution` (`ConvolutionWeights`, `Space.convolution`),
`Translations` (`TranslationWeights`, `Space.translate`, `Space.translate_translate`,
`CompactOpenSubgroup.conj`, `mem_conjSubgroup`) and `TestFunctions`
(`schwartzBruhat_mem_levelSubmodule`). From the representation-theory part of the Library
it imports `Langlands.Representation.Hecke.ActionProjection`
(`Hecke.heckeAction_normalizedIndicator_of_fixed`, `Hecke.heckeAction_normalizedIndicator_mem`,
and through it `Hecke.HeckeAlgebra.normalizedIndicator`, `Hecke.heckeAction`,
`Hecke.integratedAction_dual`), `Langlands.Representation.Smooth.FixedVectors.Definitions`
(`fixedVectors`, `fixedVectorsMap`) and `Langlands.Representation.Smooth.FixedVectors.OrderProof`
(`fixedVectors_antitone`); `contragredientMap` comes from
`Langlands.Representation.Smooth.Contragredient.Definitions`, imported through
`SchwartzAction`.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI
10.1017/S1474748003000082. Printed page numbers; the PDF page is the printed page minus
234.

- Proposition III.7.1 (printed p. 273, PDF p. 39): for an orbit `O` and a polynomial `p` on
  `O`, every admissible tempered `(π, V)` carries an operator `π(p) ∈ End_G V` such that
  "(i) si `(π_1, V_1)` et `(π_2, V_2)` sont deux représentations admissibles tempérées de
  `G` et `f ∈ Hom_G(V_1, V_2)`, `π_2(p) ∘ f = f ∘ π_1(p)`", together with (ii) and (iii).
- Proof of Proposition III.7.1 (printed p. 274, PDF p. 40), first part: for a compact open
  subgroup `H`, "`ε_H(g) = 0` si `g ∉ H`, `(mes H)⁻¹` si `g ∈ H`". The functions
  `ϕ_H = ϕ ψ_H ∈ C(G)` satisfy "(1) si `g ∈ G`, `ρ(g)λ(g)ϕ_H = ϕ_{gHg⁻¹}` ; (2) si `H'`
  est un sous-groupe ouvert compact de `G` contenant `H`, `ϕ_H ∗ ε_{H'} = ϕ_{H'}`." Then:
  "Soient `(π, V)` une représentation admissible tempérée de `G` et `v ∈ V`. Soit `H(v)`
  un sous-groupe ouvert compact de `G` fixant `v`. On vérifie grâce à (2) que si
  `H ⊂ H(v)`, `π(ϕ_H)v = π(ϕ_{H(v)})v`. On définit un opérateur `π[ϕ] ∈ End_ℂ V` par
  `π[ϕ]v = π(ϕ_H)v`, où `H` est n'importe quel sous-groupe ouvert compact de `G` fixant
  `v`. Pour `g ∈ G`, on a `π(g)π(ϕ_H)π(g⁻¹) = π(ρ(g)λ(g)ϕ_H)`. On montre alors grâce à
  (1) que `π[ϕ] ∈ End_G V`."
- I.6 (printed p. 249, PDF p. 15): `ρ(g)f(x) = f(xg)` and `λ(g)f(x) = f(g⁻¹x)`; so
  `ρ(g)λ(g)f` is `x ↦ f(g⁻¹ x g)`, which is `Space.translate ht g g f`.

The proof uses only properties (1) and (2) of the family `H ↦ ϕ_H`. This module therefore
works with an arbitrary family having these two properties (`IdempotentFamily`), not with
Waldspurger's concrete family `ϕ_H = ϕ ψ_H`.

Derived statements not displayed in the source: `exists_compactOpenSubgroup_fixed`,
`rho_mem_fixedVectors_conj`, `isBiInvariant_normalizedIndicator` and
`schwartzAction_normalizedIndicator` (that `π(ε_H)` is the Hecke-algebra action of the
normalized indicator) are standard facts used implicitly in the passages quoted above.
`schwartzAction_normalizedIndicator_of_mem` (`π(ε_H)v = v` for `H`-fixed `v`) is the step
behind "grâce à (2)". `schwartzAction_intertwining` (`π(f)` commutes with intertwiners) is
the step behind (i) for `π[ϕ]`; the source does not display it.

## Scope: abstract data and explicit hypotheses

As in `SchwartzAction`, `G` is a topological group, the weights `Ξ, σ : G → ℝ` are
arbitrary, and a representation `ρ : Representation ℂ G V` carries `hρ : IsAdmissible ρ`
and `hT : HasTemperedCoefficients Ξ σ ρ` (Waldspurger's "admissible tempérée" is replaced by
this displayed coefficient-growth hypothesis); `π(f)` is `schwartzAction hw hρ hT f` with
`hw : L2Weights μ Ξ σ`. Nothing is proved here about Waldspurger's own `Ξ`, `σ` or Haar
measure. The hypotheses of each result are:

- `exists_compactOpenSubgroup_fixed`: `[IsTopologicalGroup G]`,
  `[Nonempty (CompactOpenSubgroup G)]`, `hρ : IsSmooth ρ`.
- `rho_mem_fixedVectors_conj`: `[IsTopologicalGroup G]` and `v` fixed by `H`.
- `isBiInvariant_normalizedIndicator`, `Space.normalizedIndicator`,
  `Space.normalizedIndicator_apply`: `[IsTopologicalGroup G]`, `[MeasurableSpace G]`, an
  arbitrary measure `μ`; `Space.normalizedIndicator` (and its `_apply` lemma) also takes
  `hΞc : Continuous Ξ`, `hΞ : ∀ g, 0 < Ξ g`, `hσc : Continuous σ`, `hσ : ∀ g, 0 ≤ σ g`
  (the hypotheses of `schwartzBruhat_mem_levelSubmodule`).
- `schwartzAction_normalizedIndicator`, `schwartzAction_normalizedIndicator_of_mem`,
  `schwartzAction_normalizedIndicator_mem`: `[BorelSpace G]`, `[MeasurableMul G]`,
  `[Nonempty (CompactOpenSubgroup G)]`, `[μ.IsHaarMeasure]`, `hw`, `hρ`, `hT`, and the four
  weight hypotheses `hΞc`, `hΞ`, `hσc`, `hσ` of `Space.normalizedIndicator`.
- `schwartzAction_intertwining`: `[OpensMeasurableSpace G]`, `[MeasurableMul G]`,
  `[Nonempty (CompactOpenSubgroup G)]`, `[μ.IsMulLeftInvariant]`, `hw`, two admissible
  representations `ρ`, `τ` with tempered coefficients (`hρ`, `hτ`, `hTρ`, `hTτ`) and an
  intertwiner `T : ρ.IntertwiningMap τ`.
- `schwartzAction_translate_conj`: as `schwartzAction_intertwining` for one representation,
  plus `ht : TranslationWeights Ξ σ` (so that `Space.translate` maps `C(G)` to itself) and
  `[μ.IsMulRightInvariant]`. Waldspurger's `G` is unimodular, so his Haar measure is right
  invariant; this is not proved here.
- `IdempotentFamily hc ht` and `IdempotentFamily.schwartzAction_eq_of_le`,
  `IdempotentFamily.schwartzAction_eq`, `IdempotentFamily.operatorFun`,
  `IdempotentFamily.operatorFun_eq`: `[BorelSpace G]`, `[SecondCountableTopology G]`,
  `[Nonempty (CompactOpenSubgroup G)]`, `[μ.IsHaarMeasure]`, `[SFinite μ]`, a subgroup `K`
  with `[CompactSpace K]`, `hc : ConvolutionWeights μ K Ξ σ` (for `Space.convolution hc`;
  its fields `continuous_xi`, `pos`, `continuous_sigma`, `nonneg` supply the weight
  hypotheses of `Space.normalizedIndicator`) and `ht : TranslationWeights Ξ σ`; the lemmas
  and `operatorFun` add `hw`, `hρ`, `hT`.
- `IdempotentFamily.operator`, `IdempotentFamily.operator_apply_of_mem`,
  `IdempotentFamily.operator_intertwining`, `IdempotentFamily.comp_operator`: as above, plus
  `[μ.IsMulRightInvariant]`; the last two take a second admissible representation `τ` with
  tempered coefficients and an intertwiner `T : ρ.IntertwiningMap τ`.

## Definitions

- `Space.normalizedIndicator μ hΞc hΞ hσc hσ H : Space Ξ σ` is `ε_H`, the Library's
  normalized indicator `Hecke.HeckeAlgebra.normalizedIndicator μ H.1 H.2`, the function
  `x ↦ (μ.real H)⁻¹ 1_H(x)` (`Space.normalizedIndicator_apply`), regarded as an element of
  `C(G)`. For a Haar measure `μ` this is Waldspurger's `ε_H`, with `mes H = μ.real H`.
- `IdempotentFamily hc ht` is a structure: a map `toFun : CompactOpenSubgroup G → Space Ξ σ`,
  `H ↦ ϕ_H`, with the fields
  - `convolution_normalizedIndicator`: for `H ≤ H'`,
    `Space.convolution hc ϕ_H ε_{H'} = ϕ_{H'}` (property (2));
  - `translate_conj`: for `g ∈ G`, `Space.translate ht g g ϕ_H = ϕ_{H.conj g}`, where
    `H.conj g = {x | g⁻¹ x g ∈ H} = gHg⁻¹` (property (1)).
- `IdempotentFamily.operatorFun Φ hw hρ hT v` is `π(ϕ_H) v` for a compact open subgroup `H`
  fixing `v` chosen by `Classical.choice` (from `exists_compactOpenSubgroup_fixed`).
- `IdempotentFamily.operator Φ hw hρ hT : ρ.IntertwiningMap ρ` is the operator
  `π[ϕ] ∈ End_G V` of the source, with underlying function `operatorFun`.

## Results

- `exists_compactOpenSubgroup_fixed`: every vector of a smooth representation is fixed by a
  compact open subgroup.
- `rho_mem_fixedVectors_conj`: if `H` fixes `v`, then `H.conj g` fixes `ρ(g) v`.
- `isBiInvariant_normalizedIndicator`: the normalized indicator is bi-invariant under `H`.
- `schwartzAction_normalizedIndicator`: `π(ε_H)` is the Hecke-algebra action
  `Hecke.heckeAction μ ρ hρ.1 (Hecke.HeckeAlgebra.normalizedIndicator μ H.1 H.2)`.
- `schwartzAction_normalizedIndicator_of_mem`: `π(ε_H) v = v` for `v` fixed by `H`.
- `schwartzAction_normalizedIndicator_mem`: `π(ε_H) v` is fixed by `H` for every `v`.
- `schwartzAction_intertwining`: `T(π_ρ(f) v) = π_τ(f)(T v)` for `f ∈ C(G)`.
- `schwartzAction_translate_conj`: `π(Space.translate ht g g f) = ρ(g) π(f) ρ(g⁻¹)`, i.e.
  the source's `π(g)π(f)π(g⁻¹) = π(ρ(g)λ(g)f)`, for every `f ∈ C(G)`.
- `IdempotentFamily.schwartzAction_eq_of_le`: for `H ≤ H'` and `v` fixed by `H'`,
  `π(ϕ_{H'}) v = π(ϕ_H) v` (the source's "grâce à (2)").
- `IdempotentFamily.schwartzAction_eq`: `π(ϕ_{H₁}) v = π(ϕ_{H₂}) v` whenever `H₁` and `H₂`
  both fix `v`.
- `IdempotentFamily.operatorFun_eq` and `IdempotentFamily.operator_apply_of_mem`:
  `π[ϕ] v = π(ϕ_H) v` for every compact open subgroup `H` fixing `v`.
- `IdempotentFamily.operator_intertwining`: `T(π_ρ[ϕ] v) = π_τ[ϕ](T v)`, the analogue of
  Proposition III.7.1 (i) for `π[ϕ]`; `IdempotentFamily.comp_operator` states it as the
  equality of intertwiners `T ∘ π_ρ[ϕ] = π_τ[ϕ] ∘ T`.

## Proof notes

- `exists_compactOpenSubgroup_fixed`: smoothness gives an open subgroup fixing `v`;
  `CompactOpenSubgroup.cofinal` gives a compact open subgroup inside it, and
  `fixedVectors_antitone` passes to it.
- `rho_mem_fixedVectors_conj`: for `x ∈ gHg⁻¹`, `ρ(x)ρ(g)v = ρ(g)ρ(g⁻¹xg)v = ρ(g)v`.
- `Space.normalizedIndicator`: the normalized indicator is a test function bi-invariant
  under `H` (`Hecke.HeckeAlgebra.normalizedIndicator_mem_biInvariant`), so it lies in the
  level-`H` submodule (`schwartzBruhat_mem_levelSubmodule`) and hence in `C(G)`
  (`levelSubmodule_le_schwartzSubmodule`).
- `schwartzAction_normalizedIndicator`: both sides are compared on smooth functionals `ℓ`
  (`ext_smoothDual`): `schwartzAction_eval` and `Hecke.integratedAction_dual` both give
  `∫_G ε_H(g) ℓ(ρ(g) v) dμ(g)`. The two following results are then
  `Hecke.heckeAction_normalizedIndicator_of_fixed` and `Hecke.heckeAction_normalizedIndicator_mem`.
- `schwartzAction_intertwining`: `ℓ ∘ T` is the smooth functional `contragredientMap T ℓ`;
  by `schwartzAction_eval` both sides are integrals of `f(g) ℓ(T ρ(g) v) = f(g) ℓ(τ(g) T v)`.
- `schwartzAction_translate_conj`: `Space.translate ht g g f` is
  `Space.translate ht g 1 (Space.translate ht 1 g f)` (`Space.translate_translate`), and
  `schwartzAction_translate_right` and `schwartzAction_translate_left` give
  `π(f) ↦ ρ(g) π(f) ↦ ρ(g) π(f) ρ(g⁻¹)`.
- `IdempotentFamily.schwartzAction_eq_of_le`: by (2) and `schwartzAction_convolution`,
  `π(ϕ_{H'}) v = π(ϕ_H) π(ε_{H'}) v = π(ϕ_H) v`. `schwartzAction_eq` applies this to
  `H₁ ∩ H₂ ≤ H₁, H₂`.
- `IdempotentFamily.operator`: additivity and homogeneity use a compact open subgroup fixing
  all vectors involved (an intersection `H₁ ∩ H₂`) and `operatorFun_eq`. For
  `G`-equivariance, if `H` fixes `v` then `gHg⁻¹` fixes `ρ(g)v`, and by (1) and
  `schwartzAction_translate_conj`,
  `π[ϕ]ρ(g)v = π(ϕ_{gHg⁻¹})ρ(g)v = ρ(g)π(ϕ_H)ρ(g⁻¹)ρ(g)v = ρ(g)π[ϕ]v`.
- `IdempotentFamily.operator_intertwining`: if `H` fixes `v`, it fixes `T v`
  (`fixedVectorsMap`), and `schwartzAction_intertwining` gives
  `T π(ϕ_H) v = π(ϕ_H) T v`.

## Relation to the Library

`Hecke.HeckeAlgebra.normalizedIndicator` and `Hecke.fixedProjection`
(`Langlands.Representation.Hecke`) are the normalized indicator and its fixed-vector
projection for the Hecke algebra of test functions; `Space.normalizedIndicator` is the same
function viewed in `C(G)`, and `schwartzAction_normalizedIndicator` identifies the two
actions. `Langlands.Jacquet.conj_mem_fixedVectors`
(`Langlands.Representation.Jacquet.StablePairingProof`) is the analogue of
`rho_mem_fixedVectors_conj` for open subgroups and `Langlands.Jacquet.conjOpenSubgroup`; it
is not imported here, to avoid depending on the Jacquet-module development for a one-line
fact about `CompactOpenSubgroup.conj`.

## Open obligations

Not formalized here:

- Waldspurger's concrete family `ϕ_H = ϕ ψ_H` for `ϕ ∈ C_c(G/G^1)` and
  `ψ_H(g) = trace[ω̌(ε_H) ω̌(g) ω̌(ε_H)]`, `ω ∈ O`, the fact that `ϕ_H ∈ C(G)` (via
  `ψ_H ∈ A(ω̌)` and the separately formalized `CoefficientCutoff`), and the verification of
  properties (1) and (2) for it.
- The computation of `π[ϕ]` for irreducible `π` (the second half of the proof, with the
  Schur orthogonality computation of `⟨π[ϕ]v, v̌⟩`), the definition of polynomials on `O`
  and of `π(p)`, and Proposition III.7.1 (ii) and (iii). Proposition III.7.1 itself remains
  open.
