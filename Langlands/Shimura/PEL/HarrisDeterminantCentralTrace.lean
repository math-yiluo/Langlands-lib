import Langlands.Shimura.PEL.DeterminantTraceCoefficient
import Langlands.Shimura.PEL.HarrisHodgeTraceNormalization

/-! # The central coefficient of the actual normalized Harris determinant -/

noncomputable section

open NumberField _root_.Algebra Module
open scoped TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.CentralSimpleUnitaryData

variable {E K A : Type}
    [Field E] [NumberField E] [IsTotallyReal E]
    [Field K] [NumberField K] [IsTotallyComplex K]
    [Algebra E K] [IsQuadraticExtension E K]
    [Ring A] [Algebra E A] [Algebra K A] [IsScalarTower E K A]
    [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ K A]
    {n : ℕ} (D : CentralSimpleUnitaryData E K A n)

section General

variable {Φ : (E →+* ℝ) → (K →+* ℂ)}
    (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)
    (hΦ : IsCMSection E K Φ)

omit [IsScalarTower ℚ K A] in
/-- The binary Hodge determinant extracts the intrinsic trace of the actual action. -/
theorem traceCoefficient_kottwitzHodgeDeterminant (a : A) :
    HodgeDeterminant.traceCoefficient (D.kottwitzHodgeDeterminant C ![1, a]) =
      LinearMap.trace ℂ (D.kottwitzHodgeModule C)
        (D.kottwitzHodgeAction C ((1 : ℂ) ⊗ₜ[ℝ] ((1 : ℝ) ⊗ₜ[ℚ] a))) := by
  let : FiniteDimensional K A := D.finite
  let : FiniteDimensional ℚ A := FiniteDimensional.trans ℚ K A
  have hf : (fun i : Fin 2 =>
      D.kottwitzHodgeAction C ((1 : ℂ) ⊗ₜ[ℝ] ((1 : ℝ) ⊗ₜ[ℚ] (![1, a] i)))) =
        ![1, D.kottwitzHodgeAction C ((1 : ℂ) ⊗ₜ[ℝ] ((1 : ℝ) ⊗ₜ[ℚ] a))] := by
    ext i
    fin_cases i <;> simp [← Algebra.TensorProduct.one_def]
  change HodgeDeterminant.traceCoefficient
    (HodgeDeterminant.polynomial
      (Module.finBasis ℂ (D.kottwitzHodgeModule C))
      (fun i : Fin 2 => D.kottwitzHodgeAction C
        ((1 : ℂ) ⊗ₜ[ℝ] ((1 : ℝ) ⊗ₜ[ℚ] (![1, a] i))))) = _
  rw [hf]
  exact HodgeDeterminant.traceCoefficient_polynomial _ _

/-- The reflex coefficient includes into the same intrinsic complex trace. -/
theorem coe_traceCoefficient_kottwitzReflexDeterminant (a : A) :
    ((HodgeDeterminant.traceCoefficient
      (D.kottwitzReflexDeterminant C hΦ ![1, a]) :
        D.kottwitzCocharacterReflexField C) : ℂ) =
      LinearMap.trace ℂ (D.kottwitzHodgeModule C)
        (D.kottwitzHodgeAction C ((1 : ℂ) ⊗ₜ[ℝ] ((1 : ℝ) ⊗ₜ[ℚ] a))) := by
  have h := HodgeDeterminant.traceCoefficient_map
    (D.kottwitzCocharacterReflexField C).val.toRingHom
    (D.kottwitzReflexDeterminant C hΦ ![1, a])
  rw [D.map_kottwitzReflexDeterminant C hΦ,
    D.traceCoefficient_kottwitzHodgeDeterminant C] at h
  exact h.symm

end General

section HarrisTaylor

variable [IsCMField K]
    {L : Type} [Field L] [NumberField L] [IsCMField L]
    [IsQuadraticExtension ℚ L] [Algebra L K]
    {τ₀ : L →+* ℂ}
    (C : HarrisSignatureCharts D.toSecondKindInvolution n
      (harrisCMSection E (algebraMap L K) τ₀))

local notation "hΦ" => isCMSection_harrisCMSection E (algebraMap L K) τ₀

/-- The normalized reflex scalar map takes the actual central coefficient to the
Harris–Taylor arithmetic trace. -/
theorem harrisTaylorReflexToCM_traceCoefficient (a : K) :
    D.harrisTaylorReflexToCM C
      (HodgeDeterminant.traceCoefficient
        (D.kottwitzReflexDeterminant C hΦ ![1, algebraMap K A a])) =
      HarrisTaylor.lieTraceValue L K n a := by
  apply D.harrisTaylorReflexToCM_of_complex_eq C
  rw [D.coe_traceCoefficient_kottwitzReflexDeterminant C hΦ]
  exact D.trace_kottwitzHodgeAction_center_harrisTaylor C a

/-- The actual binary central determinant with the explicit normalized CM coefficients. -/
def harrisTaylorCentralDeterminant (a : K) : MvPolynomial (Fin 2) K :=
  D.kottwitzReflexDeterminantBaseChange C hΦ ![1, algebraMap K A a]
    (D.harrisTaylorReflexToCM C).toRingHom

/-- Its extracted linear coefficient is precisely the prescribed arithmetic value. -/
theorem traceCoefficient_harrisTaylorCentralDeterminant (a : K) :
    HodgeDeterminant.traceCoefficient (D.harrisTaylorCentralDeterminant C a) =
      HarrisTaylor.lieTraceValue L K n a := by
  unfold harrisTaylorCentralDeterminant kottwitzReflexDeterminantBaseChange
  rw [HodgeDeterminant.traceCoefficient_map]
  exact D.harrisTaylorReflexToCM_traceCoefficient C a

open CategoryTheory _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof

variable {S : Scheme.{0}} (p : S ⟶ Spec (.of K))

/-- Actual section coefficients recover the prescribed trace through the same CM map. -/
theorem traceCoefficient_harrisTaylorCentralDeterminant_section
    (a : K) (U : S.Opens) :
    HodgeDeterminant.traceCoefficient
      (MvPolynomial.map (secHom p U).hom (D.harrisTaylorCentralDeterminant C a)) =
      HarrisTaylor.lieTraceSection L p n a U := by
  rw [HodgeDeterminant.traceCoefficient_map,
    D.traceCoefficient_harrisTaylorCentralDeterminant C]
  rfl

/-- The binary reflex polynomial at the normalized scheme structure has this same
actual arithmetic section coefficient. -/
theorem traceCoefficient_reflexDeterminant_harrisTaylor_section
    (a : K) (U : S.Opens) :
    HodgeDeterminant.traceCoefficient
      (MvPolynomial.map (secHom (D.harrisTaylorReflexStructure C p) U).hom
        (D.kottwitzReflexDeterminant C hΦ ![1, algebraMap K A a])) =
      HarrisTaylor.lieTraceSection L p n a U := by
  rw [D.secHom_harrisTaylorReflexStructure C p]
  change HodgeDeterminant.traceCoefficient
    (MvPolynomial.map ((secHom p U).hom.comp (D.harrisTaylorReflexToCM C).toRingHom)
      (D.kottwitzReflexDeterminant C hΦ ![1, algebraMap K A a])) = _
  rw [← MvPolynomial.map_map]
  exact D.traceCoefficient_harrisTaylorCentralDeterminant_section C p a U

end HarrisTaylor

section RankThree

variable [IsCMField K] [IsQuadraticExtension ℚ K]
    {τ₀ : K →+* ℂ}
    (C : HarrisSignatureCharts D.toSecondKindInvolution n
      (harrisCMSection E (algebraMap K K) τ₀))

/-- In the imaginary-quadratic rank-three case, an anti-invariant central element
has the Harris–Taylor coefficient `-3*a`. -/
theorem traceCoefficient_harrisTaylorCentralDeterminant_rank_three
    (hn : n = 3) (a : K) (ha : IsCMField.complexConj K a = -a) :
    HodgeDeterminant.traceCoefficient (D.harrisTaylorCentralDeterminant C a) =
      -3 * a := by
  rw [D.traceCoefficient_harrisTaylorCentralDeterminant C]
  simp [HarrisTaylor.lieTraceValue, hn, ha, map_ofNat]
  ring

end RankThree

end Langlands.Shimura.CentralSimpleUnitaryData
