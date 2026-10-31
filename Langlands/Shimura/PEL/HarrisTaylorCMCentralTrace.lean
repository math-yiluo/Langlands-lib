import Langlands.Shimura.PEL.HarrisTaylorCMLieDeterminant

/-! # The normalized determinant forces the full Harris–Taylor central trace -/

noncomputable section

open CategoryTheory _root_.AlgebraicGeometry
open Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v

namespace Langlands.AbelianScheme

variable {S : Scheme.{u}} {R : CommRingCat.{u}} [Algebra ℚ R]
    (p : S ⟶ Spec R) (B : AbelianScheme S)
    {O : Type v} [Ring O] (α : O →+* End0 B)
    {U : S.Opens} {I : Type u} [Fintype I]

/-- The binary polynomial of an actual unital rational Lie action extracts its actual trace. -/
theorem lieRationalSectionDeterminant_traceCoefficient
    (e : SheafOfModules.free (R := S.ringCatSheaf.over U) I ≅ B.Lie.over U)
    (a : O) (V : Over U) :
    Langlands.Shimura.HodgeDeterminant.traceCoefficient
      (lieRationalSectionDeterminant p B α e ![1, a] V) =
        lieRationalSectionTrace p B α e a V := by
  classical
  rw [lieRationalSectionDeterminant_eq_basis p B α e ![1, a] V
    (localSectionBasis e V)]
  have hf :
      (fun k : Fin 2 => lieRationalSectionOrderAction p B α V (![1, a] k)) =
        ![1, lieRationalSectionOrderAction p B α V a] := by
    ext k
    fin_cases k <;> simp
  rw [hf, Langlands.Shimura.HodgeDeterminant.traceCoefficient_polynomial,
    lieRationalSectionTrace_eq_trace]

end Langlands.AbelianScheme

namespace Langlands.Shimura.HarrisTaylor

open NumberField

variable (L F : Type) [Field L] [NumberField L] [IsCMField L]
    [Field F] [NumberField F] [IsCMField F] [Algebra L F]

/-- The prescribed arithmetic trace as an additive map on the entire CM field. -/
def lieTraceValueAddHom (n : ℕ) : F →+ F where
  toFun := lieTraceValue L F n
  map_zero' := lieTraceValue_zero L F n
  map_add' := lieTraceValue_add L F n

@[simp]
theorem lieTraceValueAddHom_apply (n : ℕ) (a : F) :
    lieTraceValueAddHom L F n a = lieTraceValue L F n a := rfl

/-- The arithmetic section trace scales by every integer, on every actual section ring. -/
theorem lieTraceSection_zsmul {S : Scheme.{0}} (p : S ⟶ Spec (.of F))
    (n : ℕ) (m : ℤ) (a : F) (U : S.Opens) :
    lieTraceSection L p n (m • a) U = m • lieTraceSection L p n a U := by
  exact map_zsmul
    ((secHom p U).hom.toAddMonoidHom.comp (lieTraceValueAddHom L F n)) m a

end Langlands.Shimura.HarrisTaylor

namespace Langlands.Shimura.CentralSimpleUnitaryData

open NumberField _root_.Algebra Langlands.AbelianScheme

variable {E F A : Type}
    [Field E] [NumberField E] [IsTotallyReal E]
    [Field F] [NumberField F] [IsTotallyComplex F] [IsCMField F]
    [Algebra E F] [IsQuadraticExtension E F]
    [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
    [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ F A]
    {n : ℕ} (D : CentralSimpleUnitaryData E F A n)
    {L : Type} [Field L] [NumberField L] [IsCMField L]
    [IsQuadraticExtension ℚ L] [Algebra L F]
    {τ₀ : L →+* ℂ}
    (C : HarrisSignatureCharts D.toSecondKindInvolution n
      (harrisCMSection E (algebraMap L F) τ₀))
    {S : Scheme.{0}} (p : S ⟶ Spec (.of F))
    (B : AbelianScheme S) (i : A →ₐ[ℚ] End0 B)

/-- The full normalized order-family determinant condition implies the prescribed
central trace for every CM scalar, in every actual Lie chart and smaller open. -/
theorem harrisTaylorCMRationalLieDeterminantCondition_centralTrace
    (h : D.HarrisTaylorCMRationalLieDeterminantCondition C p B i) :
    HarrisTaylor.CentralLieTraceCondition L p B i n := by
  intro U I _ e a V
  obtain ⟨m, hm, hmem⟩ :=
    D.exists_int_multiple_mem_harrisHodgePELIntegralOrder C (algebraMap F A a)
  let c : D.harrisHodgePELIntegralOrder C := ⟨m • algebraMap F A a, hmem⟩
  have hc : (c : A) = algebraMap F A (m • a) :=
    (map_zsmul (algebraMap F A) m a).symm
  have hcoef := D.harrisTaylorCMRationalLieDeterminantConditionAt_centralCoefficient
    C p B i e (m • a) c hc V (h (Fin 2) ![1, c] U I e V)
  rw [lieRationalSectionDeterminant_traceCoefficient] at hcoef
  have htrace :
      lieRationalSectionTrace p B (D.harrisRationalOrderAction C B i) e c V =
        lieRationalSectionTrace p B (HarrisTaylor.centralAction B i) e (m • a) V := by
    change localSectionTrace e ((lieMap0 p (i (c : A))).over U) V =
      localSectionTrace e ((lieMap0 p (i (algebraMap F A (m • a)))).over U) V
    rw [hc]
  rw [htrace, HarrisTaylor.lieTraceSection_zsmul] at hcoef
  have hscale :
      lieRationalSectionTrace p B (HarrisTaylor.centralAction B i) e (m • a) V =
        m • lieRationalSectionTrace p B (HarrisTaylor.centralAction B i) e a V :=
    map_zsmul (lieRationalSectionTraceAddHom p B (HarrisTaylor.centralAction B i) e V) m a
  rw [hscale, zsmul_eq_mul, zsmul_eq_mul] at hcoef
  have hunit : IsUnit (m : Γ(S, V.left)) := by
    have hf : IsUnit (m : F) := isUnit_iff_ne_zero.mpr (Int.cast_ne_zero.mpr hm)
    simpa only [map_intCast] using hf.map (secHom p V.left).hom
  exact hunit.mul_left_cancel hcoef

/-- The normalized determinant together with the actual prescribed geometric dimension.
The central trace is derived, rather than imposed as an additional test. -/
def HarrisTaylorCMDeterminantDimensionCondition : Prop :=
  D.HarrisTaylorCMRationalLieDeterminantCondition C p B i ∧
    HarrisTaylor.PrescribedRelativeDimension E B n

/-- Adding the source numerical test to the normalized determinant is equivalent to
adding only its actual geometric dimension conjunct. -/
theorem harrisTaylorCMDeterminantDimensionCondition_iff :
    D.HarrisTaylorCMDeterminantDimensionCondition C p B i ↔
      D.HarrisTaylorCMRationalLieDeterminantCondition C p B i ∧
        HarrisTaylor.NumericalCondition L p E B i n := by
  constructor
  · rintro ⟨hdet, hdim⟩
    exact ⟨hdet, hdim,
      D.harrisTaylorCMRationalLieDeterminantCondition_centralTrace C p B i hdet⟩
  · rintro ⟨hdet, hdim, _⟩
    exact ⟨hdet, hdim⟩

end Langlands.Shimura.CentralSimpleUnitaryData
