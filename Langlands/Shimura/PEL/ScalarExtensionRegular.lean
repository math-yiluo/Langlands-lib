import Langlands.Shimura.PEL.ScalarExtensionTopology
import Langlands.Shimura.PEL.TraceSimilitudesTopology

/-! # The regular-module specialization of scalar-extension similitudes -/

noncomputable section
open scoped TensorProduct

namespace Langlands.Shimura.PEL

variable (A R : Type*) [Ring A] [Algebra ℚ A] [CommRing R] [Algebra ℚ R]

/-- For the regular source module, the extended action is left multiplication
by the tensor with its factors commuted. -/
theorem scalarExtensionRegular_smul (a : A ⊗[ℚ] R) (x : R ⊗[ℚ] A) :
    letI := scalarExtensionAlgebraModule A A R
    a • x = Algebra.TensorProduct.comm ℚ A R a * x := by
  let _ := scalarExtensionAlgebraModule A A R
  induction a using TensorProduct.inductionOn with
  | add a b ha hb => rw [add_smul, ha, hb, map_add, add_mul]
  | tmul a r =>
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => rw [smul_add, hx, hy, mul_add]
    | tmul s b =>
      rw [scalarExtensionAlgebraModule_tmul_smul]
      simp only [Algebra.TensorProduct.comm_tmul,
        Algebra.TensorProduct.tmul_mul_tmul, smul_eq_mul]

/-- Reinterpret the same operator as linear for the regular tensor algebra. -/
def scalarExtensionRegularOperator :
    letI := scalarExtensionAlgebraModule A A R
    ((R ⊗[ℚ] A) ≃ₗ[A ⊗[ℚ] R] (R ⊗[ℚ] A)) ≃*
      ((R ⊗[ℚ] A) ≃ₗ[R ⊗[ℚ] A] (R ⊗[ℚ] A)) := by
  letI := scalarExtensionAlgebraModule A A R
  let forward (e : (R ⊗[ℚ] A) ≃ₗ[A ⊗[ℚ] R] (R ⊗[ℚ] A)) :
      (R ⊗[ℚ] A) ≃ₗ[R ⊗[ℚ] A] (R ⊗[ℚ] A) :=
    { toEquiv := e.toEquiv
      map_add' := e.map_add
      map_smul' := fun a x => by
        change e (a * x) = a * e x
        have h := e.map_smul ((Algebra.TensorProduct.comm ℚ A R).symm a) x
        simpa only [scalarExtensionRegular_smul,
          AlgEquiv.apply_symm_apply, smul_eq_mul] using h }
  let backward (e : (R ⊗[ℚ] A) ≃ₗ[R ⊗[ℚ] A] (R ⊗[ℚ] A)) :
      (R ⊗[ℚ] A) ≃ₗ[A ⊗[ℚ] R] (R ⊗[ℚ] A) :=
    { toEquiv := e.toEquiv
      map_add' := e.map_add
      map_smul' := fun a x => by
        rw [scalarExtensionRegular_smul, scalarExtensionRegular_smul]
        exact e.map_smul (Algebra.TensorProduct.comm ℚ A R a) x }
  exact
    { toFun := forward
      invFun := backward
      left_inv := fun e => LinearEquiv.ext fun _ => rfl
      right_inv := fun e => LinearEquiv.ext fun _ => rfl
      map_mul' := fun e f => LinearEquiv.ext fun _ => rfl }

variable (ψ : LinearMap.BilinForm ℚ A)

/-- Scalar-extension similitudes of the regular rational module are precisely
the regular tensor-algebra similitudes, with unchanged operators and multiplier. -/
def scalarExtensionRegularSimilitudesEquiv :
    ScalarExtensionSimilitudes A A R ψ ≃*
      bilinearSimilitudes (R ⊗[ℚ] A) (ψ.baseChange R) := by
  letI := scalarExtensionAlgebraModule A A R
  exact
    { toFun := fun g => ⟨(scalarExtensionRegularOperator A R g.val.1, g.val.2), g.property⟩
      invFun := fun g => ⟨((scalarExtensionRegularOperator A R).symm g.val.1, g.val.2), g.property⟩
      left_inv := fun g => Subtype.ext (Prod.ext
        ((scalarExtensionRegularOperator A R).symm_apply_apply g.val.1) rfl)
      right_inv := fun g => Subtype.ext (Prod.ext
        ((scalarExtensionRegularOperator A R).apply_symm_apply g.val.1) rfl)
      map_mul' := fun g h => Subtype.ext (Prod.ext
        ((scalarExtensionRegularOperator A R).map_mul g.val.1 h.val.1) rfl) }

@[simp] theorem scalarExtensionRegularSimilitudesEquiv_apply
    (g : ScalarExtensionSimilitudes A A R ψ) (x : R ⊗[ℚ] A) :
    (scalarExtensionRegularSimilitudesEquiv A R ψ g).val.1 x = g.val.1 x := rfl

@[simp] theorem scalarExtensionRegularSimilitudesEquiv_inverse_apply
    (g : ScalarExtensionSimilitudes A A R ψ) (x : R ⊗[ℚ] A) :
    (scalarExtensionRegularSimilitudesEquiv A R ψ g).val.1.symm x =
      g.val.1.symm x := rfl

@[simp] theorem scalarExtensionRegularSimilitudesEquiv_symm_apply
    (g : bilinearSimilitudes (R ⊗[ℚ] A) (ψ.baseChange R)) (x : R ⊗[ℚ] A) :
    ((scalarExtensionRegularSimilitudesEquiv A R ψ).symm g).val.1 x = g.val.1 x := rfl

@[simp] theorem scalarExtensionRegularSimilitudesEquiv_multiplier
    (g : ScalarExtensionSimilitudes A A R ψ) :
    (scalarExtensionRegularSimilitudesEquiv A R ψ g).val.2 = g.val.2 := rfl

/-- Reinterpreting linearity preserves the actual operator topology in both
directions, since the two operator coordinates and multiplier do not change. -/
def scalarExtensionRegularContinuousEquiv [TopologicalSpace R] :
    letI : TopologicalSpace (R ⊗[ℚ] A) := moduleTopology R (R ⊗[ℚ] A)
    letI : TopologicalSpace
        (bilinearSimilitudes (R ⊗[ℚ] A) (ψ.baseChange R)) :=
      regularBilinearTopology (ψ.baseChange R)
    ScalarExtensionSimilitudePoints A A R ψ ≃ₜ*
      bilinearSimilitudes (R ⊗[ℚ] A) (ψ.baseChange R) := by
  letI : TopologicalSpace (R ⊗[ℚ] A) := moduleTopology R (R ⊗[ℚ] A)
  letI : TopologicalSpace
      (bilinearSimilitudes (R ⊗[ℚ] A) (ψ.baseChange R)) :=
    regularBilinearTopology (ψ.baseChange R)
  exact
    { toMulEquiv := scalarExtensionRegularSimilitudesEquiv A R ψ
      continuous_toFun := continuous_induced_rng.mpr continuous_induced_dom
      continuous_invFun := continuous_induced_rng.mpr continuous_induced_dom }

end Langlands.Shimura.PEL

namespace Langlands.Shimura.CentralSimpleUnitaryData

open NumberField Module _root_.Algebra

variable {E K A : Type*}
    [Field E] [NumberField E] [IsTotallyReal E]
    [Field K] [NumberField K] [IsTotallyComplex K]
    [Algebra E K] [IsQuadraticExtension E K]
    [Ring A] [Algebra E A] [Algebra K A] [IsScalarTower E K A]
    [Algebra ℚ A] [IsScalarTower ℚ E A]
    {n : ℕ} (D : CentralSimpleUnitaryData E K A n)
    (β : Aˣ) (hβ : D.involution (β : A) = -(β : A))
    (R : Type*) [CommRing R] [Algebra ℚ R] [TopologicalSpace R]

/-- The regular source-module scalar-extension points are precisely the existing
Harris bilinear points, with their actual operator topologies. -/
def harrisScalarExtensionBilinearContinuousEquiv :
    PEL.ScalarExtensionSimilitudePoints A A R
        ((D.skewTwist β hβ).tracePairing β⁻¹) ≃ₜ*
      D.HarrisBilinearPoints β hβ R :=
  PEL.scalarExtensionRegularContinuousEquiv A R
    ((D.skewTwist β hβ).tracePairing β⁻¹)

omit [IsScalarTower E K A] in
@[simp] theorem harrisScalarExtensionBilinearContinuousEquiv_apply
    (g : PEL.ScalarExtensionSimilitudePoints A A R
      ((D.skewTwist β hβ).tracePairing β⁻¹)) (x : R ⊗[ℚ] A) :
    (D.harrisScalarExtensionBilinearContinuousEquiv β hβ R g).val.1 x =
      g.val.1 x := rfl

omit [IsScalarTower E K A] in
@[simp] theorem harrisScalarExtensionBilinearContinuousEquiv_symm_apply
    (g : D.HarrisBilinearPoints β hβ R) (x : R ⊗[ℚ] A) :
    ((D.harrisScalarExtensionBilinearContinuousEquiv β hβ R).symm g).val.1 x =
      g.val.1 x := rfl

omit [IsScalarTower E K A] in
@[simp] theorem harrisScalarExtensionBilinearContinuousEquiv_multiplier
    (g : PEL.ScalarExtensionSimilitudePoints A A R
      ((D.skewTwist β hβ).tracePairing β⁻¹)) :
    HarrisBilinearPoints.multiplier D β hβ R
        (D.harrisScalarExtensionBilinearContinuousEquiv β hβ R g) =
      PEL.ScalarExtensionSimilitudePoints.multiplier g := rfl

/-- The original Harris involution group acts on the scalar-extended regular
source through right multiplication, preserving the actual multiplier. -/
def harrisScalarExtensionContinuousEquiv [IsTopologicalRing R] :
    (D.toSecondKindInvolution.rationalInvolution.Points R)ᵐᵒᵖ ≃ₜ*
      PEL.ScalarExtensionSimilitudePoints A A R
        ((D.skewTwist β hβ).tracePairing β⁻¹) :=
  (D.harrisTraceSimilitudesContinuousEquiv β hβ R).trans
    (D.harrisScalarExtensionBilinearContinuousEquiv β hβ R).symm

@[simp] theorem harrisScalarExtensionContinuousEquiv_apply [IsTopologicalRing R]
    (g : (D.toSecondKindInvolution.rationalInvolution.Points R)ᵐᵒᵖ)
    (x : R ⊗[ℚ] A) :
    (D.harrisScalarExtensionContinuousEquiv β hβ R g).val.1 x =
      x * (g.unop.val.1 : R ⊗[ℚ] A) := rfl

@[simp] theorem harrisScalarExtensionContinuousEquiv_multiplier [IsTopologicalRing R]
    (g : (D.toSecondKindInvolution.rationalInvolution.Points R)ᵐᵒᵖ) :
    PEL.ScalarExtensionSimilitudePoints.multiplier
        (D.harrisScalarExtensionContinuousEquiv β hβ R g) =
      AlgebraInvolution.Points.multiplier
        D.toSecondKindInvolution.rationalInvolution R g.unop := rfl

/-- The actual finite adelic Harris points agree with the scalar-extension
similitudes used to index the full compact-open Weil level tower. -/
def harrisFiniteAdelicScalarExtensionContinuousEquiv :
    D.toSecondKindInvolution.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ ≃ₜ*
      PEL.ScalarExtensionSimilitudePoints A A (Langlands.Global.FiniteAdeles ℚ)
        ((D.skewTwist β hβ).tracePairing β⁻¹) :=
  D.harrisScalarExtensionContinuousEquiv β hβ (Langlands.Global.FiniteAdeles ℚ)

/-- The same comparison over the actual away finite adeles, with arbitrary
natural modulus and in particular at a prime modulus. -/
def harrisPrimeToScalarExtensionContinuousEquiv (m : ℕ) :
    (D.toSecondKindInvolution.rationalInvolution.Points
        (Langlands.Global.PrimeToFiniteAdeles m))ᵐᵒᵖ ≃ₜ*
      PEL.ScalarExtensionSimilitudePoints A A
        (Langlands.Global.PrimeToFiniteAdeles m)
        ((D.skewTwist β hβ).tracePairing β⁻¹) :=
  D.harrisScalarExtensionContinuousEquiv β hβ (Langlands.Global.PrimeToFiniteAdeles m)

end Langlands.Shimura.CentralSimpleUnitaryData
