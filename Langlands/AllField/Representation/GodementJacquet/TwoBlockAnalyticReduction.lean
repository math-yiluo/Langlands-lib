import Langlands.Representation.GodementJacquet.TwoBlockAnalyticReduction
import Langlands.AllField.Representation.GodementJacquet.TwoBlockAnalyticReversal
import Langlands.AllField.Representation.GodementJacquet.TwoBlockMatrixAnalyticInductionStatement
/-!
# Reduction of two-block matrix analytics to ordinary induction

The ordinary analytic induction statement below has no Fourier-data premise.
Its use on the actual reversed inverse-transpose blocks supplies the transformed
conclusion of the published conditional statement.
-/

noncomputable section

namespace Langlands.AllField.GodementJacquet
open Langlands.GodementJacquet hiding TwoBlockMatrixAnalyticInductionStatement TwoBlockOrdinaryMatrixAnalyticInductionStatement inverseTransposeProductReversalEquiv iotaMatrixAnalyticAssertions_product_iff twoBlockMatrixAnalyticInduction_of_ordinary
open Langlands.AllField.GodementJacquet

open Langlands.HarmonicAnalysis

universe uF uV

/-- The ordinary two-block induction assertion, with only ordinary block
analytics, admissibility and specified scalar central quasicharacters as
representation hypotheses. This proposition is not proved in this module. -/
def TwoBlockOrdinaryMatrixAnalyticInductionStatement : Prop :=
  ∀ (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F],
    ∀ (t : ℕ) (m : Fin 2 → ℕ) (h : ∑ i, (m i + 1) = t + 1)
      (V : Fin 2 → Type uV) [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
      (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (V i))
      (ω : Fin 2 → Quasicharacter F),
      (∀ i, Classification.HasGLCentralCharacter F (m i + 1) (σ i)
        (ω i : Fˣ →* ℂˣ)) →
      (∀ i, IsSmooth (σ i)) →
      (∀ i, IsAdmissible (σ i)) →
      ∀ P : Fin 2 → Polynomial ℂ,
      (∀ i, Langlands.AllField.GodementJacquet.Padic.MatrixAnalyticAssertions F (σ i) (P i)) →
      Langlands.AllField.GodementJacquet.Padic.MatrixAnalyticAssertions F
        ((⟨⟩ : LocalFieldData F).normalizedProductInduced (RankinSelberg.succBlockShape m h) σ)
        (∏ i, P i)

/-- Ordinary analytic induction, applied to both the original and the actual
reversed inverse-transpose block families, proves the complete published
conditional two-block analytic statement. -/
theorem twoBlockMatrixAnalyticInduction_of_ordinary
    (hordinary : TwoBlockOrdinaryMatrixAnalyticInductionStatement.{uF,uV}) :
    TwoBlockMatrixAnalyticInductionStatement.{uF,uV} := by
  intro F _ _ _ _
  let := IsTopologicalAddGroup.rightUniformSpace F
  let := isUniformAddGroup_of_addCommGroup (G := F)
  let := rowFourierCutoff_nonarchimedean (K := F)
  let := borel F
  let : BorelSpace F := ⟨rfl⟩
  intro t m h V hadd hmod σ ψ ν _hν ω hω hσ hadm Pi PDual c a hdata
  refine ⟨hordinary F t m h V σ ω hω hσ hadm Pi (fun i => (hdata i).1), ?_⟩
  let : ∀ i : Fin 2, AddCommGroup (V i.rev) := fun i => hadd i.rev
  let : ∀ i : Fin 2, Module ℂ (V i.rev) := fun i => hmod i.rev
  have hadmR := isAdmissible_reversedInverseTransposeBlocks m σ hadm
  have hωR : ∀ i : Fin 2,
      Classification.HasGLCentralCharacter F (m i.rev + 1)
        (reversedInverseTransposeBlocks m σ i)
        ((ω i.rev)⁻¹ : Fˣ →* ℂˣ) := by
    intro i
    exact Classification.hasGLCentralCharacter_comp_inverseTranspose (hω i.rev)
  have hblockR :=
    Langlands.AllField.GodementJacquet.Padic.matrixAnalyticAssertions_reversedInverseTransposeBlocks F m σ PDual
      (fun i => (hdata i).2.1)
  have hindR := hordinary F t (fun i : Fin 2 => m i.rev)
    (sum_reversedSuccBlocks m h) (fun i : Fin 2 => V i.rev)
    (reversedInverseTransposeBlocks m σ) (fun i : Fin 2 => (ω i.rev)⁻¹)
    hωR (fun i => (hadmR i).1) hadmR (fun i : Fin 2 => PDual i.rev) hblockR
  exact (Langlands.AllField.GodementJacquet.Padic.iotaMatrixAnalyticAssertions_succBlocks_iff F m h σ hσ PDual).mpr hindR

end Langlands.AllField.GodementJacquet
