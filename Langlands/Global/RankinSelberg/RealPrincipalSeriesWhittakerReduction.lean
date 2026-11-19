import Langlands.Global.RankinSelberg.RealPrincipalSeriesReduction

/-! # Restriction and extension of real principal-series coefficient maps -/

noncomputable section

open Langlands.Archimedean Langlands.LocalFactor.Archimedean
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

namespace RealPrincipalSeries

private theorem realInducedBlockAt_expand (ds : List RealBlock) (p : ℕ) :
    realInducedBlockAt (expand ds) p = none := by
  induction ds generalizing p with
  | nil => rfl
  | cons d ds ih =>
    cases d with
    | character d =>
      cases p with
      | zero => rfl
      | succ p => exact ih p
    | induced d =>
      rcases p with _ | _ | p
      · rfl
      · rfl
      · exact ih p

/-- The expanded standard module is the full position principal series. -/
theorem realStandardModule_expand (n : ℕ) (ds : List RealBlock) :
    realStandardModule n (expand ds) = principalSeries ℝ n (realPositionCharacter ds) := by
  have hχ : realPositionCharacter (expand ds) = realPositionCharacter ds :=
    funext fun p => funext fun a => realPositionCharacter_expand ds p a
  ext f
  rw [mem_realStandardModule_iff, hχ]
  refine ⟨And.left, fun hf => ⟨hf, ?_⟩⟩
  intro p d hd
  rw [realInducedBlockAt_expand] at hd
  cases hd

/-- On the source of a coefficient map, expansion gives the inclusion of K-finite functions. -/
theorem realStandardKFinite_le_expand (n : ℕ) (ds : List RealBlock) :
    Automorphic.realStandardKFinite n ds ≤ Automorphic.realStandardKFinite n (expand ds) := by
  intro f hf
  exact ⟨realStandardModule_expand n ds ▸ hf.1.1, hf.2⟩

private theorem restrict_uniformIntertwiner {r : ℕ} {ds es : List RealBlock} {a : ℝˣ}
    (h : Automorphic.realStandardKFinite (r + 1) ds ≤ Automorphic.realStandardKFinite (r + 1) es)
    {B : Automorphic.realStandardKFinite (r + 1) es →ₗ[ℂ]
      (Langlands.GeneralLinear (r + 1) ℝ → ℂ)}
    (hB : IsRealUniformWhittakerIntertwiner r es a B) :
    IsRealUniformWhittakerIntertwiner r ds a (B.comp (Submodule.inclusion h)) := by
  obtain ⟨⟨hψ, hSmooth, hGrowth, hK, hLie⟩, N, hN⟩ := hB
  let ι := Submodule.inclusion h
  exact ⟨⟨fun f => hψ (ι f), fun f => hSmooth (ι f), fun f => hGrowth (ι f),
    fun k f f' hf => hK k (ι f) (ι f') hf, fun X f f' hf => hLie X (ι f) (ι f') hf⟩,
    N, fun f => hN (ι f)⟩

private theorem model_le_of_source_eq {r : ℕ} {ds es : List RealBlock} (a : ℝˣ)
    (h : Automorphic.realStandardKFinite (r + 1) ds = Automorphic.realStandardKFinite (r + 1) es) :
    realUniformWhittakerModel r ds a ≤ realUniformWhittakerModel r es a := by
  refine iSup_le fun B => iSup_le fun hB => ?_
  refine le_iSup_of_le (B.comp (Submodule.inclusion h.ge))
    (le_iSup_of_le (restrict_uniformIntertwiner h.ge hB) ?_)
  rintro _ ⟨f, rfl⟩
  refine ⟨Submodule.inclusion h.le f, ?_⟩
  exact congrArg B (Subtype.ext rfl)

/-- With only zero induction weights, all the rotation vanishing clauses are vacuous,
and expansion gives the same uniform coefficient space. -/
theorem realUniformWhittakerModel_expand_of_zero_weights (r : ℕ) (ds : List RealBlock) (a : ℝˣ)
    (hZero : ∀ p d, realInducedBlockAt ds p = some d → d.weight = 0) :
    realUniformWhittakerModel r (expand ds) a = realUniformWhittakerModel r ds a := by
  have hS : realStandardModule (r + 1) (expand ds) = realStandardModule (r + 1) ds := by
    rw [realStandardModule_expand]
    refine le_antisymm (fun f hf => ⟨hf, ?_⟩) (fun f hf => hf.1)
    intro p d hd k hk
    rw [hZero p d hd, abs_zero] at hk
    exact (not_lt_of_ge (abs_nonneg k) hk).elim
  have hK : Automorphic.realStandardKFinite (r + 1) (expand ds) =
      Automorphic.realStandardKFinite (r + 1) ds := by
    unfold Automorphic.realStandardKFinite
    rw [hS]
  exact le_antisymm (model_le_of_source_eq a hK) (model_le_of_source_eq a hK.symm)

end RealPrincipalSeries

open RealPrincipalSeries

/-- Uniform coefficient maps extend along the source inclusion when a nonzero
induction weight imposes a rotation condition. -/
def RealUniformPrincipalSeriesExtensionStatement : Prop :=
  ∀ (r : ℕ) (ds : List RealBlock), realRank ds = r + 1 →
    (∃ p d, realInducedBlockAt ds p = some d ∧ d.weight ≠ 0) →
  ∀ (a : ℝˣ) (B : Automorphic.realStandardKFinite (r + 1) ds →ₗ[ℂ]
    (Langlands.GeneralLinear (r + 1) ℝ → ℂ)),
    IsRealUniformWhittakerIntertwiner r ds a B →
      ∃ C : Automorphic.realStandardKFinite (r + 1) (expand ds) →ₗ[ℂ]
          (Langlands.GeneralLinear (r + 1) ℝ → ℂ),
        IsRealUniformWhittakerIntertwiner r (expand ds) a C ∧
          C.comp (Submodule.inclusion (realStandardKFinite_le_expand (r + 1) ds)) = B

/-- The coefficient extension premise for nonzero weights implies the full
uniform-model inclusion used by the principal-series reduction. -/
def RealUniformPrincipalSeriesExtensionReductionStatement : Prop :=
  RealUniformPrincipalSeriesExtensionStatement → RealUniformPrincipalSeriesInclusionStatement

theorem realUniformPrincipalSeriesExtensionReduction :
    RealUniformPrincipalSeriesExtensionReductionStatement := by
  intro hExt r ds hRank a
  by_cases hZero : ∀ p d, realInducedBlockAt ds p = some d → d.weight = 0
  · rw [realUniformWhittakerModel_expand_of_zero_weights r ds a hZero]
  · push Not at hZero
    refine iSup_le fun B => iSup_le fun hB => ?_
    obtain ⟨C, hC, hComp⟩ := hExt r ds hRank hZero a B hB
    refine le_iSup_of_le C (le_iSup_of_le hC ?_)
    rintro _ ⟨f, rfl⟩
    exact ⟨Submodule.inclusion (realStandardKFinite_le_expand (r + 1) ds) f,
      LinearMap.congr_fun hComp f⟩

end Langlands.Global.RankinSelbergGlobal
