# Waldspurger, Lemma I.6.1 for left translation

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.AdmissibleCoefficientSpaceLeft`,
namespace `Langlands.HarishChandraSchwartz`. It imports:

- `Langlands.HarmonicAnalysis.GroupAction`: `leftFunctions` (`λ(g) f = f(g⁻¹ ·)` on `G → ℂ`)
  and `leftFunctions_apply`;
- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.AdmissibleCoefficientSpace` (Worker 249):
  `rightTranslateSpan`, `twoSidedTranslateSpan`, `IsRightAdmissible`, `evalFunctional`,
  `isSmoothVector_evalFunctional`, `mem_span_evalFunctional`, `orbitSpanMap`,
  `orbitSpanMap_surjective`, `isRightAdmissible_iff`; through it `Whittaker.rightTranslation`
  (`ρ`), `coefficientFunctionSpace`, `matrixCoefficient_mem_coefficientFunctionSpace`, `translate`,
  `IsBiInvariant`, `FiniteVectors.orbitSubrepresentation`, `FiniteVectors.action_mem_orbitSpan`,
  `CompactOpenSubgroup.cofinal`, `isAdmissible_of_injective` and
  `SphericalExistence.isAdmissible_of_surjective`;
- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.L2`: `check` (`f̌(g) = f(g⁻¹)`),
  `check_apply`, `check_check`, `IsBiInvariant.check`;
- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.TraceFamilyScalar`: `contragredientRep`
  (the smooth contragredient `ω̌` bundled as a `SmoothRep`);
- `Langlands.Representation.Smooth.Contragredient.AdmissibleDualityProof`:
  `isAdmissible_smoothContragredient_of_compact_cofinal`,
  `smoothBidual_surjective_of_compact_cofinal` (with `smoothBidual`, `smoothContragredient`);
- `Langlands.Representation.Smooth.Contragredient.ExactProof`:
  `contragredientMap_surjective_of_injective_of_compact_cofinal` (with `contragredientMap`).

## Provenance

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082
(literature id `waldspurger-2003-plancherel`). Printed page numbers; the PDF page is the printed
page minus 234. The quoted text carries no overline (checked on the rendered PDF page 15).

- I.6, printed p. 249 (PDF p. 15): "Pour `f ∈ C_lisse(G)`, notons `V_ρ(f)`, resp. `V_λ(f)`,
  resp. `V_{ρ×λ}(f)`, le plus petit sous-espace de `C_lisse(G)` contenant `f` et stable par `ρ`,
  resp. `λ`, resp. `ρ × λ`. Notons `ρ_f`, resp. `λ_f`, la représentation déduite de `ρ` dans
  `V_ρ(f)`, resp. de `λ` dans `V_λ(f)`. Notons `A_ρ`, resp. `A_λ`, l'ensemble des
  `f ∈ C_lisse(G)` telles que `ρ_f`, resp. `λ_f`, soit admissible."
- Lemme I.6.1, printed p. 249: "(1) Soit `f ∈ A_ρ`, resp. `A_λ`. Alors `V_{ρ×λ}(f) = A(ρ_f)`,
  resp. `= A(λ̌_f)`. (2) On a l'égalité `A_ρ = A_λ = A(G)`." The proof treats `ρ` and says
  "Un raisonnement analogue vaut si `f ∈ A_λ`."

## Correspondence and generalizations

- The setting is that of `AdmissibleCoefficientSpace`: `G` a topological group, with a compact
  open subgroup from `IsLeftAdmissible` on; functions are all of `G → ℂ`; `A(G)` is the union
  of the `A(π)` over admissible `π` on carriers in the universe of `G`.
- `λ` is the Library's `leftFunctions` (`λ(g) f = f(g⁻¹ ·)`), `V_λ(f)` is
  `leftTranslateSpan f`, `λ_f` its representation, `A_λ` is `IsLeftAdmissible f`
  (bi-invariance under a compact open subgroup and admissibility of `λ_f`), and `λ̌_f` is the
  smooth contragredient of `λ_f` (the Library's `contragredientRep`).
- Instead of repeating the source's argument for `λ`, the module transports the statements for
  `ρ` along `f ↦ f̌`, which intertwines `λ` with `ρ`; this route is derived. The step for (1)
  uses the source's description of the smooth dual of `V_ρ(f̌)` by point evaluations and the
  reflexivity of the admissible `λ_f` (`smoothBidual_surjective_of_compact_cofinal`).
- Derived results, not statements of the paper: `checkIntertwiningMap`, `checkIntertwiningMap_apply`, `checkIntertwiningMap_injective`,
  `leftRightCheck`, `leftRightCheck_apply`, `leftRightCheck_injective`,
  `leftRightCheck_surjective`, `translate_mem_twoSidedTranslateSpan_left`,
  `isLeftAdmissible_iff_check`, `check_mem_coefficientFunctionSpace`,
  `exists_admissible_coefficient_check`.

## Scope and hypotheses

- `leftTranslateSpan`, `checkIntertwiningMap`, `leftRightCheck` and their
  lemmas, and `translate_mem_twoSidedTranslateSpan_left` (a function `v ∈ V_λ(f)` and `y : G`)
  hold for any group `G : Type u`.
- `IsLeftAdmissible` needs a topological group; `check_mem_coefficientFunctionSpace` takes
  `A : SmoothRep.{0, u, u} ℂ G` and `f ∈ coefficientFunctionSpace A`.
- With `[Nonempty (CompactOpenSubgroup G)]`: `isLeftAdmissible_iff_check`,
  `exists_admissible_coefficient_check` (an admissible `A` with `f ∈ A(A)`),
  `isLeftAdmissible_iff`, and `twoSidedTranslateSpan_eq_coefficientFunctionSpace_left`
  (`hf : IsLeftAdmissible f`).

## Definitions

- `leftTranslateSpan f` (`V_λ(f)`, the `λ`-orbit span of `f` in `G → ℂ`),
  `IsLeftAdmissible f` (`f ∈ A_λ`).
- `checkIntertwiningMap`: `f ↦ f̌` as an intertwiner from `λ` to `ρ`; `leftRightCheck f`: its
  restriction `V_λ(f) → V_ρ(f̌)`, a bijective intertwiner.

## Results

- `isLeftAdmissible_iff_check`: `f ∈ A_λ` iff `f̌ ∈ A_ρ`.
- `check_mem_coefficientFunctionSpace`: `f ∈ A(π)` implies `f̌ ∈ A(π̌)`;
  `exists_admissible_coefficient_check`: `A(G)` is stable under `f ↦ f̌`.
- `isLeftAdmissible_iff` (**Lemma I.6.1 (2) for `λ`**): `A_λ = A(G)`.
- `twoSidedTranslateSpan_eq_coefficientFunctionSpace_left` (**Lemma I.6.1 (1) for `λ`**):
  `V_{ρ×λ}(f) = A(λ̌_f)` for `f ∈ A_λ`.

## Proof notes

1. `checkIntertwiningMap`: `(λ(g) f)ˇ(x) = f(g⁻¹ x⁻¹) = f̌(x g) = (ρ(g) f̌)(x)`; it maps
   `V_λ(f)` onto `V_ρ(f̌)` (`orbitSpanMap_surjective`), injectively.
2. `isLeftAdmissible_iff_check`: bi-invariance passes through `IsBiInvariant.check`;
   admissibility through the bijective intertwiner `leftRightCheck f`
   (`isAdmissible_of_surjective`, `isAdmissible_of_injective`).
3. `check_mem_coefficientFunctionSpace`: `ℓ(π(g⁻¹) x)` is the coefficient of `π̌` at `ℓ` and the
   evaluation at `x` (`smoothBidual`); `A(π̌)` is admissible for admissible `π`.
4. `isLeftAdmissible_iff`: `f ∈ A_λ` iff `f̌ ∈ A_ρ = A(G)` iff `f ∈ A(G)` (step 3 and
   `check_check`).
5. `twoSidedTranslateSpan_eq_coefficientFunctionSpace_left`: the evaluation at `y` on `V_λ(f)`
   is smooth, as the pullback along `leftRightCheck f` of the evaluation at `y⁻¹` on
   `V_ρ(f̌)`; then `x ↦ f(g₂⁻¹ x g₁)` is the coefficient of `λ̌_f` at the evaluation at `g₁`
   and the bidual image of `λ(g₂) f`. Conversely, a coefficient of `λ̌_f` is, by the
   reflexivity of `λ_f`, `g ↦ ℓ(λ_f(g⁻¹) x)`; `ℓ` is the pullback of a smooth form on
   `V_ρ(f̌)` (`contragredientMap_surjective_of_injective_of_compact_cofinal`), a combination of
   evaluations (`mem_span_evalFunctional`), so the coefficient is a combination of the
   functions `g ↦ x(g y⁻¹)`, which lie in `V_{ρ×λ}(f)`
   (`translate_mem_twoSidedTranslateSpan_left`).
