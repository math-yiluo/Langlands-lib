import Langlands.Automorphic.GroupSchemeFullAEL2FiniteApproximationStatement
import Langlands.Automorphic.GroupSchemeQuotientL2FiniteApproximationProof

/-! # One convergent finite approximation on the original ambient and cusp spaces -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory Filter
open scoped CategoryTheory.MonObj Topology

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.PositiveRealTorus Langlands.GroupScheme Langlands.Analysis

/-- The original cusp inclusion transfers convergence for the same subgroup sequence. -/
theorem groupSchemeFullAEL2FiniteApproximation :
    GroupSchemeFullAEL2FiniteApproximationStatement.{u} := by
  intro F _ _ G _ _ hPD hG T i hi _ I _ e hc _
  obtain ⟨K, hK, hb, hAfixed, hAconv, hAdense⟩ :=
    groupSchemeQuotientL2FiniteApproximation F G T i hi I e hc
  let S := fullAEL2CuspidalSubmodule F G hPD hG T i hi I e hc
  let A := fun n =>
    letI : CompactSpace (K n) := isCompact_iff_compactSpace.mp (hK n)
    haarQuotientL2FiniteAverage F G T i hi I e hc (K n)
  let B := fun n =>
    letI : CompactSpace (K n) := isCompact_iff_compactSpace.mp (hK n)
    fullAEL2CuspidalFiniteAverage F G hPD hG T i hi I e hc (K n)
  have hBfixed : ∀ n (ψ : S),
      B n ψ ∈ Langlands.fixedVectors
        (fullAEL2CuspidalFiniteRightAction F G hPD hG T i hi I e hc)
        (K n).toSubgroup := by
    intro n ψ
    let : CompactSpace (K n) := isCompact_iff_compactSpace.mp (hK n)
    exact fullAEL2CuspidalFiniteAverage_mem_fixedVectors F G hPD hG T i hi I e hc (K n) ψ
  have hval : ∀ n (ψ : S), (B n ψ).val = A n ψ.val := by
    intro n ψ
    let : CompactSpace (K n) := isCompact_iff_compactSpace.mp (hK n)
    exact fullAEL2CuspidalFiniteAverage_val F G hPD hG T i hi I e hc (K n) ψ
  have hBconv : ∀ ψ : S, Tendsto (fun n => B n ψ) atTop (𝓝 ψ) := by
    intro ψ
    apply tendsto_subtype_rng.mpr
    simpa only [hval] using hAconv ψ.val
  have hBdense : Dense {ψ : S |
      Langlands.IsSmoothVector
        (fullAEL2CuspidalFiniteRightAction F G hPD hG T i hi I e hc) ψ} := by
    intro ψ
    exact mem_closure_of_tendsto (hBconv ψ)
      (Eventually.of_forall (fun n => ⟨K n, hBfixed n ψ⟩))
  refine ⟨K, hK, hb, hAfixed, hAconv, hAdense, hBfixed, hBconv, hBdense, hval, ?_, ?_⟩
  · intro n φ
    let : CompactSpace (K n) := isCompact_iff_compactSpace.mp (hK n)
    exact fullAEL2CuspidalOrthogonalProjection_finiteAverage F G hPD hG T i hi I e hc (K n) φ
  · intro n φ
    let : CompactSpace (K n) := isCompact_iff_compactSpace.mp (hK n)
    exact fullAEL2CuspidalAmbientProjection_finiteAverage F G hPD hG T i hi I e hc (K n) φ

end Langlands.Automorphic.GroupSchemeFunctions
