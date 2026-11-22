import Langlands.Global.AdelicEisensteinPointwiseAutomorphyStatement
import Langlands.Global.AdelicEisensteinContinuationComparison
import Langlands.Automorphic.GroupSchemePositiveMatrixEmbedding

/-! # Automorphy of pointwise Eisenstein continuations -/

universe u

open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

/-- Pointwise Eisenstein continuations inherit automorphy on a common
open dense domain from the published local Fréchet-valued continuation. -/
theorem eisensteinPointwiseContinuationAutomorphyReduction :
    EisensteinPointwiseContinuationAutomorphyReductionStatement.{u} := by
  intro hcont F _ _ G P M U A _ _ _ _ p _ iU l a r _ _ _ hA hT hG hU
    K hK N d rho hsmooth hcalc φ hmax hrho hφ EP DP hEP hEPagree n e
  obtain ⟨N', rho', hN', hrho', htransfer⟩ :=
    exists_positiveMatrixEmbedding_of_isClosedSubgroup rho hrho hsmooth hcalc
  have hφ' := (htransfer _ _ φ).mp hφ
  obtain ⟨EC, hEC, hlocal⟩ := hcont F G P M U A p iU l a r hA hT hG hU
    K hK rho' hN' hrho' hsmooth hcalc φ hmax hφ'
  obtain ⟨R₁, hR₁⟩ := hEPagree
  obtain ⟨R₂, hR₂⟩ := hEC
  have hagree : ∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam → EP lam = EC lam := by
    refine ⟨max R₁ R₂, fun lam hreg => ?_⟩
    have hreg₁ : r.IsRegularParameter hA hT R₁ lam :=
      fun α hα => lt_of_le_of_lt (le_max_left _ _) (hreg α hα)
    have hreg₂ : r.IsRegularParameter hA hT R₂ lam :=
      fun α hα => lt_of_le_of_lt (le_max_right _ _) (hreg α hα)
    exact (hR₁ lam hreg₁).trans (hR₂ lam hreg₂).symm
  obtain ⟨S, hS, hdS, _, hauto, heq⟩ :=
    exists_openDense_eisensteinContinuation_eqOn r hA hT rho' hN' hrho' hsmooth hcalc
      e hEP hagree (hlocal n e)
  have hD := (hEP 1).2 n e
  refine ⟨(e ⁻¹' DP) ∩ S, hD.1.inter hS, hD.2.1.inter_of_isOpen_right hdS hS,
    Set.inter_subset_left, fun s hs => ?_⟩
  have hs' := heq hs
  change EP (e s) = EC (e s) at hs'
  rw [hs']
  exact (htransfer _ _ _).mpr (hauto s hs.2)

end Langlands.Global
