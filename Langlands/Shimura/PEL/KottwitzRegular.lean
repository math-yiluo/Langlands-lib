import Langlands.Shimura.PEL.TraceSimilitudesBaseChange

/-! # Kottwitz's complex homomorphism on the actual regular PEL module -/

noncomputable section

universe u v w z

open scoped TensorProduct

namespace Langlands.Shimura.AlgebraInvolution.ComplexHom

variable {B : Type*} [Ring B] [Algebra ℝ B]
    {σ : AlgebraInvolution ℝ B}

/-- Right multiplication by the commuting complex image is an algebra
homomorphism into the endomorphisms of the left regular module. -/
def rightRegular (h : ComplexHom σ) : ℂ →ₐ[ℝ] Module.End B B where
  toFun z := LinearMap.mulRight B (h.hom z)
  map_one' := by
    apply LinearMap.ext
    intro x
    change x * h.hom 1 = x
    rw [_root_.map_one, mul_one]
  map_mul' z t := by
    apply LinearMap.ext
    intro x
    change x * h.hom (z * t) = (x * h.hom t) * h.hom z
    rw [mul_comm z t, _root_.map_mul, mul_assoc]
  map_zero' := by
    apply LinearMap.ext
    intro x
    change x * h.hom 0 = 0
    rw [_root_.map_zero, mul_zero]
  map_add' z t := by
    apply LinearMap.ext
    intro x
    change x * h.hom (z + t) = x * h.hom z + x * h.hom t
    rw [_root_.map_add, mul_add]
  commutes' r := by
    apply LinearMap.ext
    intro x
    change x * h.hom (algebraMap ℝ ℂ r) = r • x
    rw [h.hom.commutes, Algebra.algebraMap_eq_smul_one,
      mul_smul_comm, mul_one]

@[simp] theorem rightRegular_apply (h : ComplexHom σ) (z : ℂ) (x : B) :
    h.rightRegular z x = x * h.hom z := rfl

/-- The operator commutes with the full left algebra action. -/
theorem rightRegular_left (h : ComplexHom σ) (z : ℂ) (b x : B) :
    h.rightRegular z (b * x) = b * h.rightRegular z x :=
  mul_assoc b x (h.hom z)

theorem rightRegular_injective [Nontrivial B] (h : ComplexHom σ) :
    Function.Injective h.rightRegular :=
  h.rightRegular.toRingHom.injective

/-- The complex structure squares to minus the identity. -/
theorem rightRegular_I_sq (h : ComplexHom σ) :
    h.rightRegular Complex.I * h.rightRegular Complex.I = -1 := by
  rw [← _root_.map_mul, Complex.I_mul_I, _root_.map_neg, _root_.map_one]

end Langlands.Shimura.AlgebraInvolution.ComplexHom

namespace Langlands.Shimura.CentralSimpleUnitaryData

open NumberField Module _root_.Algebra

variable {E : Type u} {K : Type v} {A : Type w}
    [Field E] [NumberField E] [IsTotallyReal E]
    [Field K] [NumberField K] [IsTotallyComplex K]
    [Algebra E K] [IsQuadraticExtension E K]
    [Ring A] [Algebra E A] [Algebra K A] [IsScalarTower E K A]
    [Algebra ℚ A] [IsScalarTower ℚ E A]
    {n : ℕ} (D : CentralSimpleUnitaryData E K A n)

omit [IsScalarTower E K A] in
/-- Scalar extension preserves the adjoint identity for left multiplication. -/
theorem tracePairingBaseChange_left (S : Type z)
    [CommRing S] [Algebra ℚ S] (β : Aˣ) (b x y : S ⊗[ℚ] A) :
    D.tracePairingBaseChange S β (b * x) y =
      D.tracePairingBaseChange S β x
        (D.toSecondKindInvolution.rationalInvolution.baseChange S b * y) := by
  rw [D.tracePairingBaseChange_apply, D.tracePairingBaseChange_apply]
  simp only [AlgebraInvolution.apply_mul, AlgebraInvolution.apply_apply]
  simpa only [mul_assoc] using congrArg
    (fun s : S => algebraMap ℚ S (n : ℚ)⁻¹ * s)
    (Langlands.Algebra.regularTrace_mul_comm S (S ⊗[ℚ] A) b
      (x * ((1 : S) ⊗ₜ[ℚ] (β : A)) *
        D.toSecondKindInvolution.rationalInvolution.baseChange S y))

variable {Φ : (E →+* ℝ) → (K →+* ℂ)}
    (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)

/-- The constructed Kottwitz homomorphism on the actual left regular PEL module. -/
def kottwitzPELHom :
    ℂ →ₐ[ℝ] Module.End (ℝ ⊗[ℚ] A) (ℝ ⊗[ℚ] A) :=
  (D.realPositiveKottwitzHom C).val.rightRegular

@[simp] theorem kottwitzPELHom_apply (z : ℂ) (x : ℝ ⊗[ℚ] A) :
    D.kottwitzPELHom C z x =
      x * (D.realPositiveKottwitzHom C).val.hom z := rfl

theorem kottwitzPELHom_left (z : ℂ) (b x : ℝ ⊗[ℚ] A) :
    D.kottwitzPELHom C z (b * x) = b * D.kottwitzPELHom C z x :=
  (D.realPositiveKottwitzHom C).val.rightRegular_left z b x

theorem kottwitzPELHom_I_sq :
    D.kottwitzPELHom C Complex.I * D.kottwitzPELHom C Complex.I = -1 :=
  (D.realPositiveKottwitzHom C).val.rightRegular_I_sq

variable (β : Aˣ) (hβ : D.involution (β : A) = -(β : A))

/-- The actual inverse-unit trace form has complex conjugation as the adjoint
of the constructed complex action. -/
theorem kottwitzPELHom_adjoint (z : ℂ) (x y : ℝ ⊗[ℚ] A) :
    (D.skewTwist β hβ).tracePairingBaseChange ℝ β⁻¹
        (D.kottwitzPELHom C z x) y =
      (D.skewTwist β hβ).tracePairingBaseChange ℝ β⁻¹ x
        (D.kottwitzPELHom C (star z) y) := by
  rw [kottwitzPELHom_apply, kottwitzPELHom_apply,
    D.skewTwist_tracePairingBaseChange_right β hβ]
  rw [(D.realPositiveKottwitzHom C).val.star_compatible]

/-- The norm-square is the multiplier on the actual real trace form. -/
theorem kottwitzPELHom_normSq (z : ℂ) (x y : ℝ ⊗[ℚ] A) :
    (D.skewTwist β hβ).tracePairingBaseChange ℝ β⁻¹
        (D.kottwitzPELHom C z x) (D.kottwitzPELHom C z y) =
      Complex.normSq z *
        (D.skewTwist β hβ).tracePairingBaseChange ℝ β⁻¹ x y := by
  rw [D.kottwitzPELHom_adjoint C β hβ]
  simp only [kottwitzPELHom_apply, mul_assoc]
  rw [← map_mul, Complex.star_def, Complex.mul_conj,
    (D.realPositiveKottwitzHom C).val.hom.map_coe_real_complex]
  rw [Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one, map_smul,
    smul_eq_mul]

/-- On units this is exactly the existing right-regular trace-similitude
realization, with its opposite-group convention retained. -/
theorem kottwitzPELHom_units_comparison (z : ℂˣ) :
    (D.harrisTraceSimilitudesEquiv ℝ β hβ
      (MulOpposite.op ((D.realPositiveKottwitzHom C).val.toSimilitudes z))).val.1.toLinearMap =
        D.kottwitzPELHom C (z : ℂ) := rfl

/-- The previously constructed Hodge form uses precisely this regular action. -/
theorem kottwitzPELHom_hodgeForm (x y : ℝ ⊗[ℚ] A) :
    (D.skewTwist β hβ).tracePairingBaseChange ℝ β⁻¹ x
        (D.kottwitzPELHom C Complex.I y) =
      D.kottwitzTraceHodgeForm β hβ C x y := rfl

end Langlands.Shimura.CentralSimpleUnitaryData
