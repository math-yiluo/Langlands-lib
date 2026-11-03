# The projection `p_χ` (Waldspurger VIII.4)

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.CentralProjection`,
namespace `Langlands.HarishChandraSchwartz`. It imports the published module
`Convolution`, from which it uses `continuous_of_mem_levelSubmodule` (elements of a level
`C_H` are continuous), together with the seminorms `nu`, the levels `levelSubmodule`, the
space `schwartzSubmodule`/`Space` and `norm_le_of_nu` of `Basic`.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI
10.1017/S1474748003000082. Printed page numbers; the PDF page is the printed page minus
234.

- VIII.4, printed p. 327 (PDF p. 93): `Â_G = {χ ∈ Hom(A_G, ℂ^×); Re(χ) = 0}`, the unitary
  characters of `A_G`; `C_lisse(G)_χ` is the space of functions bi-invariant under a compact
  open subgroup with `f(a g) = χ(a) f(g)` for `a ∈ A_G`; the map `p_χ : C(G) → C_lisse(G)_χ`
  is `(p_χ f)(g) = ∫_{A_G} χ^{-1}(a) f(a g) da`, and "the integral is absolutely
  convergent".
- Proof of Proposition VIII.4.1, printed p. 328 (PDF p. 94): "one checks easily that for
  every `f ∈ p_χ(°C(G))` and every `r ∈ ℝ` there is `c > 0` such that
  `|f(g)| ≤ c Ξ(g) (1 + σ(g))^{-r}` for every `g ∈ G¹`".

## Scope: abstract data and explicit hypotheses

`G` is a group, `A` a subgroup with a measurable structure and a measure `μ_A` (no Haar
property is assumed), `Ξ, σ : G → ℝ` arbitrary weights and `χ : A →* ℂˣ` a homomorphism.
Waldspurger's data would be `A = A_G` with its Haar measure, `Ξ` of II.1, `σ` of I.1 and
`χ ∈ Â_G`; none of the hypotheses below is proved here for these data.

- `CentralWeights μ_A Ξ σ` (a structure of five hypotheses): `Ξ(g) > 0`; `σ(g) ≥ 0`;
  `Ξ(a g) = Ξ(g)` for `a ∈ A`; `1 + σ(a) ≤ (1 + σ(a g)) (1 + σ(g))` for `a ∈ A` (for
  Waldspurger's `σ`, a consequence of `σ(xy) ≤ σ(x) + σ(y)` and `σ(g^{-1}) = σ(g)`, I.1);
  and `∫_A (1 + σ(a))^{-r₀} dμ_A(a) < ∞` for some `r₀`.
- `IsUnitaryCharacter χ` (a structure of two hypotheses): `|χ(a)| = 1` for all `a`
  (Waldspurger's `Re(χ) = 0`) and `a ↦ χ(a)` is measurable.

Further hypotheses of individual results are listed with them below.

## Definitions

- `CentralWeights μA Ξ σ` and `IsUnitaryCharacter χ`, as above.
- `centralProjection μA χ f g = ∫_A χ(a)^{-1} f(a g) dμ_A(a)` (Waldspurger's `p_χ`).
- `Space.centralProjection hw hχ : Space Ξ σ →ₗ[ℂ] (G → ℂ)`, the map `f ↦ p_χ f` on
  `C(G)` (requires the instances of the integrability results below).

## Results

- `rpow_neg_two_mul_le`: for real `x, y ≥ 1`, `C > 0`, `t ≥ 0` and `x + y - 1 ≤ C z`,
  `z^{-2t} ≤ (C²)^t x^{-t} y^{-t}`.
- `IsUnitaryCharacter.norm_inv`, `.enorm_inv`, `.measurable_inv`: `|χ(a)^{-1}| = 1` and
  `a ↦ χ(a)^{-1}` is measurable.
- `CentralWeights.rpow_neg_le`: `(1 + σ(a g))^{-s} ≤ (1 + σ(g))^s (1 + σ(a))^{-s}` for
  `a ∈ A`, `s ≥ 0`.
- `CentralWeights.enorm_le`: if `s ≥ 0` and `ν_s(f) < ∞`, then
  `|f(a g)| ≤ ν_s(f) Ξ(g) (1 + σ(g))^s (1 + σ(a))^{-s}`.
- `CentralWeights.lintegral_enorm_le`: under the same hypotheses,
  `∫_A |f(a g)| dμ_A ≤ ν_s(f) Ξ(g) (1 + σ(g))^s ∫_A (1 + σ(a))^{-s} dμ_A`.
- `CentralWeights.exists_lintegral_lt_top`: some `s ≥ 0` has
  `∫_A (1 + σ(a))^{-s} dμ_A < ∞`.
- `CentralWeights.enorm_centralProjection_le`: for unitary `χ`, `s ≥ 0` and `ν_s(f) < ∞`,
  `|p_χ f(g)| ≤ ν_s(f) Ξ(g) (1 + σ(g))^s ∫_A (1 + σ(a))^{-s} dμ_A`.
- `CentralWeights.enorm_centralProjection_le_rpow_neg` (the estimate in the proof of
  VIII.4.1): for unitary `χ`, a set `S ⊆ G` and `C > 0` with
  `1 + σ(g) + σ(a) ≤ C (1 + σ(a g))` for all `g ∈ S`, `a ∈ A` (hypothesis `hS`; for
  Waldspurger, `S = G¹`, and this is the input of his "one checks easily"), and `f` with
  `ν_r(f) < ∞` for every `r`: for every `r` there is a finite `c` with
  `|p_χ f(g)| ≤ c Ξ(g) (1 + σ(g))^{-r}` for all `g ∈ S`. It applies to every such `f`, not
  only to cuspidal ones.
- `centralProjection_mul_left`: if `A` has a measurable multiplication and `μ_A` is right
  invariant (Waldspurger's `A_G` is commutative, so its Haar measure is), then
  `(p_χ f)(b g) = χ(b) (p_χ f)(g)` for `b ∈ A`, for every `f` and every homomorphism `χ`.
- `IsBiInvariant.centralProjection`: if `A ≤ Z(G)` (hypothesis `hA`) and `f` is
  bi-invariant under a subgroup `H`, so is `p_χ f`.
- `CentralWeights.integrable_of_mem_level` and `.integrable_mul_of_mem_level`: if `G` is a
  topological group, `A` has the subspace topology with open sets measurable
  (`OpensMeasurableSpace A`) and `f ∈ C_H` for a compact open subgroup `H`, then
  `a ↦ f(a g)` and, for unitary `χ`, `a ↦ χ(a)^{-1} f(a g)` are integrable: the integral
  defining `p_χ f(g)` converges absolutely.
- `CentralWeights.integrable_mul_of_mem`: the same for `f ∈ C(G)`, when `G` has a compact
  open subgroup (`Nonempty (CompactOpenSubgroup G)`).
- `Space.centralProjection_apply`: `Space.centralProjection hw hχ f = p_χ f`.

Together, for central `A`, right invariant `μ_A` and `f ∈ C_H`, the results show that `p_χ f`
is defined by an absolutely convergent integral, is bi-invariant under `H` and is
`χ`-covariant, i.e. lies in Waldspurger's `C_lisse(G)_χ`.

## Proof notes

The pointwise bound combines `|f(a g)| ≤ ν_s(f) Ξ(a g)(1 + σ(a g))^{-s}` (`norm_le_of_nu`),
`Ξ(a g) = Ξ(g)` and `1 + σ(a) ≤ (1 + σ(a g))(1 + σ(g))`. For the estimate on `S`, take
`t = max(r, r₀, 0)` and use `ν_{2t}`: from `1 + σ(g) + σ(a) ≤ C(1 + σ(a g))` and
`(1 + σ(g))(1 + σ(a)) ≤ (1 + σ(g) + σ(a))²` one gets
`(1 + σ(a g))^{-2t} ≤ (C²)^t (1 + σ(g))^{-t} (1 + σ(a))^{-t}`, and integrating over `A`
gives the bound with `c = ν_{2t}(f) (C²)^t ∫_A (1 + σ(a))^{-r₀} dμ_A`. Covariance is the
substitution `a ↦ a b` (right invariance), and bi-invariance follows because central `a`
commutes with `H`. Integrability uses the continuity of elements of `C_H` and the bound of
`χ^{-1}` by one.

## Open obligations

For Waldspurger's data: the realization of `A_G` with its Haar measure and of `Â_G`, the
invariance `Ξ(a g) = Ξ(g)` for `a ∈ A_G`, the convergence of `∫_{A_G} (1 + σ(a))^{-r₀} da`,
and the comparison `1 + σ(g) + σ(a) ≤ C(1 + σ(a g))` on `G¹ × A_G` are not proved here; nor
is the finite dimensionality of `p_χ(°C_H)` (Proposition VIII.4.1).
