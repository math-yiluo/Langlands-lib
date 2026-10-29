import Langlands.Shimura.PEL.IntegralPairing
import Langlands.Shimura.PEL.HarrisIntegralOrder

/-! # An integer alternating pairing for the actual Harris regular module -/

noncomputable section

universe u v w

namespace Langlands.Shimura.CentralSimpleUnitaryData

open NumberField _root_.Algebra

variable {E : Type u} {K : Type v} {A : Type w}
    [Field E] [NumberField E] [IsTotallyReal E]
    [Field K] [NumberField K] [IsTotallyComplex K]
    [Algebra E K] [IsQuadraticExtension E K]
    [Ring A] [Algebra E A] [Algebra K A] [IsScalarTower E K A]
    [Algebra ℚ A] [IsScalarTower ℚ E A]
    {n : ℕ} {Φ : (E →+* ℝ) → (K →+* ℂ)}
    (D : CentralSimpleUnitaryData E K A n)
    (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)

/-- Scale the existing rational regular lattice so that its fixed form is integer-valued. -/
def harrisHodgePELIntegralLattice : Submodule ℤ A :=
  PEL.integralPairingLattice (D.harrisHodgePELForm C) D.harrisHodgePELLattice

instance harrisHodgePELIntegralLattice_isLattice :
    Submodule.IsLattice ℚ (D.harrisHodgePELIntegralLattice C) :=
  PEL.integralPairingLattice_isLattice _ _

theorem harrisHodgePELIntegralLattice_isInteger
    (x y : D.harrisHodgePELIntegralLattice C) :
    IsLocalization.IsInteger ℤ (D.harrisHodgePELForm C (x : A) (y : A)) :=
  PEL.integralPairingLattice_isInteger _ _ x y

/-- The constructed integer restriction of the unchanged normalized Harris trace form. -/
def harrisHodgePELIntegralPairing :
    LinearMap.BilinForm ℤ (D.harrisHodgePELIntegralLattice C) :=
  PEL.integerPairing (D.harrisHodgePELForm C) _
    (D.harrisHodgePELIntegralLattice_isInteger C)

@[simp] theorem harrisHodgePELIntegralPairing_cast
    (x y : D.harrisHodgePELIntegralLattice C) :
    (D.harrisHodgePELIntegralPairing C x y : ℚ) =
      D.harrisHodgePELForm C (x : A) (y : A) :=
  PEL.integerPairing_cast _ _ _ x y

theorem harrisHodgePELIntegralPairing_isAlt :
    (D.harrisHodgePELIntegralPairing C).IsAlt :=
  PEL.integerPairing_isAlt _ _ _ (D.harrisHodgePELForm_isAlt C)

theorem harrisHodgePELIntegralPairing_nondegenerate :
    (D.harrisHodgePELIntegralPairing C).Nondegenerate :=
  PEL.integerPairing_nondegenerate _ _ _
    (Submodule.IsLattice.span_eq_top (A := ℚ))
    (D.harrisHodgePELForm_nondegenerate C)

private theorem harrisIntegralOrder_le_stabilizer :
    D.harrisHodgePELIntegralOrder C ≤ PEL.latticeStabilizer D.harrisHodgePELLattice :=
  fun _ ha _ hx => D.harrisHodgePELIntegralOrder_mul_mem_lattice C ha hx

theorem harrisHodgePELIntegralOrder_mul_mem_integralLattice
    {a x : A} (ha : a ∈ D.harrisHodgePELIntegralOrder C)
    (hx : x ∈ D.harrisHodgePELIntegralLattice C) :
    a * x ∈ D.harrisHodgePELIntegralLattice C :=
  PEL.latticeStabilizer_le_integralPairingLatticeStabilizer _ _
    (harrisIntegralOrder_le_stabilizer D C ha) x hx

/-- The same positive-involution order acts on the scaled lattice by left multiplication. -/
def harrisHodgePELIntegralPairingAction :
    D.harrisHodgePELIntegralOrder C →+*
      Module.End ℤ (D.harrisHodgePELIntegralLattice C) :=
  (PEL.integralPairingLatticeAction (D.harrisHodgePELForm C)
    D.harrisHodgePELLattice).comp
    (Subalgebra.inclusion (harrisIntegralOrder_le_stabilizer D C)).toRingHom

@[simp] theorem harrisHodgePELIntegralPairingAction_apply
    (a : D.harrisHodgePELIntegralOrder C) (x : D.harrisHodgePELIntegralLattice C) :
    (D.harrisHodgePELIntegralPairingAction C a x : A) = (a : A) * x := rfl

theorem harrisHodgePELIntegralPairingAction_injective :
    Function.Injective (D.harrisHodgePELIntegralPairingAction C) := by
  intro a b h
  have he := PEL.integralPairingLatticeAction_injective
    (D.harrisHodgePELForm C) D.harrisHodgePELLattice h
  exact Subtype.ext (congrArg (fun x : PEL.latticeStabilizer D.harrisHodgePELLattice =>
    (x : A)) he)

theorem harrisHodgePELIntegralPairingAction_adjoint
    (a : D.harrisHodgePELIntegralOrder C) (x y : D.harrisHodgePELIntegralLattice C) :
    D.harrisHodgePELIntegralPairing C (D.harrisHodgePELIntegralPairingAction C a x) y =
      D.harrisHodgePELIntegralPairing C x
        (D.harrisHodgePELIntegralPairingAction C (D.harrisHodgePELIntegralInvolution C a) y) := by
  apply Int.cast_injective (α := ℚ)
  simpa only [harrisHodgePELIntegralPairing_cast,
    harrisHodgePELIntegralPairingAction_apply, harrisHodgePELIntegralInvolution_apply] using
    D.harrisHodgePELForm_left C (a : A) (x : A) (y : A)

end Langlands.Shimura.CentralSimpleUnitaryData
