import Langlands.Shimura.PEL.KottwitzRegular
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Charpoly.Basic

/-! # The Hodge summand of the regular PEL module -/

noncomputable section
universe u v w
open scoped TensorProduct

namespace Langlands.Shimura.RegularHodge

variable {B : Type u} [Ring B] [Algebra ℝ B]
    (h : ℂ →ₐ[ℝ] B)

/-- Complexification of the given homomorphism, retaining the real source. -/
def complexifiedHom : ℂ →ₐ[ℝ] ℂ ⊗[ℝ] B :=
  (Algebra.TensorProduct.includeRight : B →ₐ[ℝ] ℂ ⊗[ℝ] B).comp h

@[simp] theorem complexifiedHom_apply (z : ℂ) :
    complexifiedHom h z = (1 : ℂ) ⊗ₜ[ℝ] h z := rfl

/-- The complex-linear extension of the right regular complex action. -/
def action : ℂ →ₐ[ℝ] Module.End ℂ (ℂ ⊗[ℝ] B) where
  toFun z := LinearMap.mulRight ℂ (complexifiedHom h z)
  map_one' := by
    apply LinearMap.ext
    intro x
    change x * complexifiedHom h 1 = x
    rw [map_one, mul_one]
  map_zero' := by
    apply LinearMap.ext
    intro x
    change x * complexifiedHom h 0 = 0
    rw [map_zero, mul_zero]
  map_add' z t := by
    apply LinearMap.ext
    intro x
    change x * complexifiedHom h (z + t) =
      x * complexifiedHom h z + x * complexifiedHom h t
    rw [map_add, mul_add]
  map_mul' z t := by
    apply LinearMap.ext
    intro x
    change x * complexifiedHom h (z * t) =
      (x * complexifiedHom h t) * complexifiedHom h z
    rw [mul_comm z t, map_mul, mul_assoc]
  commutes' r := by
    apply LinearMap.ext
    intro x
    change x * complexifiedHom h (algebraMap ℝ ℂ r) = r • x
    rw [(complexifiedHom h).commutes, Algebra.algebraMap_eq_smul_one,
      mul_smul_comm, mul_one]

@[simp] theorem action_apply (z : ℂ) (x : ℂ ⊗[ℝ] B) :
    action h z x = x * complexifiedHom h z := rfl

@[simp] theorem action_tmul (z c : ℂ) (b : B) :
    action h z (c ⊗ₜ[ℝ] b) = c ⊗ₜ[ℝ] (b * h z) := by
  simp only [action_apply, complexifiedHom_apply,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one]

theorem action_I_sq : action h Complex.I * action h Complex.I = -1 := by
  rw [← map_mul, Complex.I_mul_I, map_neg, map_one]

theorem action_I_twice (x : ℂ ⊗[ℝ] B) :
    action h Complex.I (action h Complex.I x) = -x := by
  exact congrArg (fun f : Module.End ℂ (ℂ ⊗[ℝ] B) => f x) (action_I_sq h)

/-- Kottwitz's `V₁`: the vectors on which every complex number acts as itself. -/
def submodule : Submodule ℂ (ℂ ⊗[ℝ] B) where
  carrier := {x | ∀ z : ℂ, action h z x = z • x}
  zero_mem' z := by simp
  add_mem' hx hy z := by rw [map_add, hx z, hy z, smul_add]
  smul_mem' c x hx z := by rw [map_smul, hx z, smul_comm]

@[simp] theorem mem_submodule (x : ℂ ⊗[ℝ] B) :
    x ∈ submodule h ↔ ∀ z : ℂ, action h z x = z • x := Iff.rfl

/-- Testing the complex structure suffices to characterize the whole summand. -/
theorem mem_submodule_iff_I (x : ℂ ⊗[ℝ] B) :
    x ∈ submodule h ↔ action h Complex.I x = Complex.I • x := by
  constructor
  · exact fun hx => hx Complex.I
  · intro hx z
    have hz : z = (z.re : ℂ) + z.im • Complex.I := by
      simpa only [Complex.real_smul] using (Complex.re_add_im z).symm
    rw [hz, map_add, map_smul]
    change action h (z.re : ℂ) x + z.im • action h Complex.I x =
      ((z.re : ℂ) + z.im • Complex.I) • x
    rw [(action h).map_coe_real_complex, hx]
    change z.re • x + z.im • (Complex.I • x) =
      (algebraMap ℝ ℂ z.re + z.im • Complex.I) • x
    rw [add_smul, smul_assoc, IsScalarTower.algebraMap_smul]

theorem submodule_eq_eigenspace :
    submodule h = (action h Complex.I).eigenspace Complex.I := by
  ext x
  rw [mem_submodule_iff_I, Module.End.mem_eigenspace_iff]

/-- The conjugate Hodge summand, using the same real homomorphism. -/
def conjugateSubmodule : Submodule ℂ (ℂ ⊗[ℝ] B) :=
  submodule (h.comp Complex.conjAe.toAlgHom)

@[simp] theorem action_conj (z : ℂ) :
    action (h.comp Complex.conjAe.toAlgHom) z = action h (star z) := rfl

theorem mem_conjugateSubmodule_iff_I (x : ℂ ⊗[ℝ] B) :
    x ∈ conjugateSubmodule h ↔ action h Complex.I x = -Complex.I • x := by
  rw [conjugateSubmodule, mem_submodule_iff_I, action_conj]
  simp only [Complex.star_def, Complex.conj_I, map_neg, LinearMap.neg_apply]
  constructor <;> intro hx <;>
    simpa only [neg_neg, neg_smul] using congrArg Neg.neg hx

/-- Full left multiplication preserves the Hodge summand. -/
theorem mul_mem (b : ℂ ⊗[ℝ] B) {x : ℂ ⊗[ℝ] B} (hx : x ∈ submodule h) :
    b * x ∈ submodule h := by
  intro z
  change (b * x) * complexifiedHom h z = z • (b * x)
  rw [mul_assoc, ← action_apply, hx z, mul_smul_comm]

/-- The actual complexified algebra acts on `V₁` by left multiplication. -/
def leftAction : (ℂ ⊗[ℝ] B) →ₐ[ℂ] Module.End ℂ (submodule h) where
  toFun b := (LinearMap.mulLeft ℂ b).restrict (fun _ hx => mul_mem h b hx)
  map_one' := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change 1 * (x : ℂ ⊗[ℝ] B) = x
    exact one_mul _
  map_zero' := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change 0 * (x : ℂ ⊗[ℝ] B) = 0
    exact zero_mul _
  map_add' b c := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (b + c) * (x : ℂ ⊗[ℝ] B) = b * x + c * x
    exact add_mul _ _ _
  map_mul' b c := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (b * c) * (x : ℂ ⊗[ℝ] B) = b * (c * x)
    exact mul_assoc _ _ _
  commutes' c := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change algebraMap ℂ (ℂ ⊗[ℝ] B) c * (x : ℂ ⊗[ℝ] B) = c • x
    exact (Algebra.smul_def c (x : ℂ ⊗[ℝ] B)).symm

@[simp] theorem leftAction_apply (b : ℂ ⊗[ℝ] B) (x : submodule h) :
    (leftAction h b x : ℂ ⊗[ℝ] B) = b * x := rfl

/-- The two Hodge summands are complementary inside the actual complexification. -/
theorem isCompl : IsCompl (submodule h) (conjugateSubmodule h) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro x hx hy
    have hp := (mem_submodule_iff_I h x).mp hx
    have hm := (mem_conjugateSubmodule_iff_I h x).mp hy
    have heq : Complex.I • x = -(Complex.I • x) := by
      simpa only [neg_smul] using hp.symm.trans hm
    have hz : (2 * Complex.I) • x = 0 := by
      rw [two_mul, add_smul]
      exact eq_neg_iff_add_eq_zero.mp heq
    exact (smul_eq_zero.mp hz).resolve_left (by simp)
  · rw [codisjoint_iff, Submodule.eq_top_iff']
    intro x
    let xp := (2 : ℂ)⁻¹ • (x - Complex.I • action h Complex.I x)
    let xm := (2 : ℂ)⁻¹ • (x + Complex.I • action h Complex.I x)
    have hp : xp ∈ submodule h := by
      rw [mem_submodule_iff_I]
      simp only [xp, map_smul, map_sub, action_I_twice, smul_neg,
        smul_smul]
      match_scalars
      all_goals ring_nf
      all_goals norm_num [Complex.I_sq]
    have hm : xm ∈ conjugateSubmodule h := by
      rw [mem_conjugateSubmodule_iff_I]
      simp only [xm, map_smul, map_add, action_I_twice, smul_neg,
        smul_smul]
      match_scalars
      all_goals ring_nf
      all_goals norm_num [Complex.I_sq]
    have heq : xp + xm = x := by
      dsimp [xp, xm]
      module
    exact Submodule.mem_sup.mpr ⟨xp, hp, xm, hm, heq⟩

/-- Addition identifies the two constructed summands with the complexified module. -/
def decomposition :
    (submodule h × conjugateSubmodule h) ≃ₗ[ℂ] ℂ ⊗[ℝ] B :=
  Submodule.prodEquivOfIsCompl _ _ (isCompl h)

@[simp] theorem decomposition_apply (x : submodule h × conjugateSubmodule h) :
    decomposition h x = (x.1 : ℂ ⊗[ℝ] B) + x.2 := rfl

section Finite
variable [FiniteDimensional ℝ B]

/-- The characteristic polynomial is computed from the constructed Hodge action. -/
def charpoly (b : ℂ ⊗[ℝ] B) : Polynomial ℂ :=
  (leftAction h b).charpoly

theorem charpoly_monic (b : ℂ ⊗[ℝ] B) : (charpoly h b).Monic :=
  LinearMap.charpoly_monic _

theorem charpoly_natDegree (b : ℂ ⊗[ℝ] B) :
    (charpoly h b).natDegree = Module.finrank ℂ (submodule h) :=
  LinearMap.charpoly_natDegree _

end Finite
end Langlands.Shimura.RegularHodge

namespace Langlands.Shimura.CentralSimpleUnitaryData

open NumberField Module _root_.Algebra
variable {E : Type u} {K : Type v} {A : Type w}
    [Field E] [NumberField E] [IsTotallyReal E]
    [Field K] [NumberField K] [IsTotallyComplex K]
    [Algebra E K] [IsQuadraticExtension E K]
    [Ring A] [Algebra E A] [Algebra K A] [IsScalarTower E K A]
    [Algebra ℚ A] [IsScalarTower ℚ E A]
    {n : ℕ} (D : CentralSimpleUnitaryData E K A n)
    {Φ : (E →+* ℝ) → (K →+* ℂ)}
    (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)

/-- The actual regular PEL Hodge module, using the fixed Kottwitz homomorphism. -/
def kottwitzHodgeModule : Submodule ℂ (ℂ ⊗[ℝ] (ℝ ⊗[ℚ] A)) :=
  RegularHodge.submodule (D.realPositiveKottwitzHom C).val.hom

/-- The defining action is the scalar extension of the published regular action. -/
theorem kottwitzHodge_complexification (z c : ℂ) (a : ℝ ⊗[ℚ] A) :
    RegularHodge.action (D.realPositiveKottwitzHom C).val.hom z
        (c ⊗ₜ[ℝ] a) =
      c ⊗ₜ[ℝ] D.kottwitzPELHom C z a :=
  RegularHodge.action_tmul _ z c a

/-- Its left action is the restriction of actual multiplication in the tensor algebra. -/
def kottwitzHodgeAction :
    (ℂ ⊗[ℝ] (ℝ ⊗[ℚ] A)) →ₐ[ℂ] Module.End ℂ (D.kottwitzHodgeModule C) :=
  RegularHodge.leftAction (D.realPositiveKottwitzHom C).val.hom

@[simp] theorem kottwitzHodgeAction_apply (b : ℂ ⊗[ℝ] (ℝ ⊗[ℚ] A))
    (x : D.kottwitzHodgeModule C) :
    (D.kottwitzHodgeAction C b x : ℂ ⊗[ℝ] (ℝ ⊗[ℚ] A)) = b * x := rfl

/-- The characteristic polynomial of a rational algebra element on actual `V₁`. -/
def kottwitzHodgeCharpoly (a : A) : Polynomial ℂ := by
  letI : FiniteDimensional K A := D.finite
  letI : FiniteDimensional ℚ A := FiniteDimensional.trans ℚ K A
  exact RegularHodge.charpoly (D.realPositiveKottwitzHom C).val.hom
    ((1 : ℂ) ⊗ₜ[ℝ] ((1 : ℝ) ⊗ₜ[ℚ] a))

end Langlands.Shimura.CentralSimpleUnitaryData
