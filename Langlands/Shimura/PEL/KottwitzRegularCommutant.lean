import Langlands.Shimura.PEL.KottwitzRegular
import Langlands.Shimura.Unitary.DivisionCondition
import Mathlib.Algebra.Algebra.Opposite
import Mathlib.Algebra.Algebra.Bilinear

/-! # The actual commutant of the regular PEL algebra action -/

noncomputable section

universe u v w

namespace Langlands.Algebra

variable (R : Type u) (A : Type v) [CommRing R] [Ring A] [Algebra R A]

/-- The full scalar-linear commutant of the actual left regular action. -/
def regularCommutant : Subalgebra R (Module.End R A) :=
  Subalgebra.centralizer R (Set.range (_root_.Algebra.lmul R A))

variable {R A}

theorem mem_regularCommutant_iff (f : Module.End R A) :
    f ∈ regularCommutant R A ↔ ∀ a x : A, f (a * x) = a * f x := by
  constructor
  · intro hf a x
    exact (congrArg (fun g : Module.End R A => g x)
      (hf (_root_.Algebra.lmul R A a) ⟨a, rfl⟩)).symm
  · intro hf g hg
    obtain ⟨a, rfl⟩ := hg
    exact LinearMap.ext (fun x => (hf a x).symm)

variable (R A)

/-- Restricting scalars identifies algebra-linear endomorphisms with the full
commutant, with the inverse using precisely the commuting condition. -/
def regularEndEquivCommutant :
    Module.End A A ≃ₐ[R] regularCommutant R A where
  toFun f := ⟨f.restrictScalars R, (mem_regularCommutant_iff _).mpr
    (fun a x => f.map_smul a x)⟩
  invFun f :=
    { toFun := f.val
      map_add' := f.val.map_add
      map_smul' := (mem_regularCommutant_iff f.val).mp f.property }
  left_inv _ := LinearMap.ext (fun _ => rfl)
  right_inv _ := Subtype.ext (LinearMap.ext (fun _ => rfl))
  map_mul' _ _ := Subtype.ext (LinearMap.ext (fun _ => rfl))
  map_add' _ _ := Subtype.ext (LinearMap.ext (fun _ => rfl))
  commutes' _ := Subtype.ext (LinearMap.ext (fun _ => rfl))

@[simp] theorem regularEndEquivCommutant_apply (f : Module.End A A) (x : A) :
    (regularEndEquivCommutant R A f).val x = f x := rfl

@[simp] theorem regularEndEquivCommutant_symm_apply
    (f : regularCommutant R A) (x : A) :
    (regularEndEquivCommutant R A).symm f x = f.val x := rfl

/-- The opposite algebra is the full commutant, via the existing Mathlib
regular endomorphism equivalence and the actual scalar restriction. -/
def regularOppositeEquivCommutant : Aᵐᵒᵖ ≃ₐ[R] regularCommutant R A :=
  (AlgEquiv.moduleEndSelf R (A := A)).trans (regularEndEquivCommutant R A)

@[simp] theorem regularOppositeEquivCommutant_apply (a : Aᵐᵒᵖ) (x : A) :
    (regularOppositeEquivCommutant R A a).val x = x * a.unop := rfl

@[simp] theorem regularOppositeEquivCommutant_symm_apply
    (f : regularCommutant R A) :
    (regularOppositeEquivCommutant R A).symm f = MulOpposite.op (f.val 1) := rfl

/-- No extra commuting operators are omitted: evaluation at one recovers the
unique multiplier of every scalar-linear operator in the commutant. -/
theorem regularCommutant_apply_eq (f : regularCommutant R A) (x : A) :
    f.val x = x * f.val 1 := by
  simpa only [mul_one] using
    (mem_regularCommutant_iff f.val).mp f.property x 1

/-- Division of the actual underlying algebra is equivalent to division of
the actual commuting algebra, rather than just of an abstract substitute. -/
theorem regularCommutant_division_iff :
    (∀ a : A, a ≠ 0 → IsUnit a) ↔
      ∀ f : regularCommutant R A, f ≠ 0 → IsUnit f := by
  let e := regularOppositeEquivCommutant R A
  constructor
  · intro h f hf
    have hpre : e.symm f ≠ 0 := by
      intro hz
      apply hf
      simpa only [map_zero, AlgEquiv.apply_symm_apply] using congrArg e hz
    have ha : (e.symm f).unop ≠ 0 := by simpa using hpre
    have hu : IsUnit (e.symm f) := (h _ ha).op
    have hv := hu.map e.toMonoidHom
    change IsUnit (e (e.symm f)) at hv
    simpa only [AlgEquiv.apply_symm_apply] using hv
  · intro h a ha
    have hne : e (MulOpposite.op a) ≠ 0 := by
      intro hz
      have : MulOpposite.op a = 0 := e.injective (by simpa using hz)
      exact ha (by simpa using this)
    have hu := (h _ hne).map e.symm.toMonoidHom
    change IsUnit (e.symm (e (MulOpposite.op a))) at hu
    rw [AlgEquiv.symm_apply_apply] at hu
    exact hu.unop

end Langlands.Algebra

namespace Langlands.Shimura.AlgebraInvolution.ComplexHom

variable {B : Type*} [Ring B] [Algebra ℝ B]
    {σ : AlgebraInvolution ℝ B}

/-- The existing regular complex action, now in the full scalar-linear
commutant of the left algebra action. -/
def rightRegularCommutant (h : ComplexHom σ) :
    ℂ →ₐ[ℝ] Langlands.Algebra.regularCommutant ℝ B :=
  (Langlands.Algebra.regularEndEquivCommutant ℝ B).toAlgHom.comp h.rightRegular

@[simp] theorem rightRegularCommutant_apply (h : ComplexHom σ) (z : ℂ) (x : B) :
    (h.rightRegularCommutant z).val x = x * h.hom z := rfl

/-- The inverse commutant comparison recovers the original complex image in
the opposite algebra, preserving right multiplication. -/
@[simp] theorem rightRegularCommutant_opposite (h : ComplexHom σ) (z : ℂ) :
    (Langlands.Algebra.regularOppositeEquivCommutant ℝ B).symm
      (h.rightRegularCommutant z) = MulOpposite.op (h.hom z) := by
  change MulOpposite.op (1 * h.hom z) = _
  rw [one_mul]

end Langlands.Shimura.AlgebraInvolution.ComplexHom

namespace Langlands.Shimura.CentralSimpleUnitaryData

open NumberField _root_.Algebra
open scoped TensorProduct

variable {E : Type u} {K : Type v} {A : Type w}
    [Field E] [NumberField E] [IsTotallyReal E]
    [Field K] [NumberField K] [IsTotallyComplex K]
    [Algebra E K] [IsQuadraticExtension E K]
    [Ring A] [Algebra E A] [Algebra K A] [IsScalarTower E K A]
    [Algebra ℚ A] [IsScalarTower ℚ E A]
    {n : ℕ} (D : CentralSimpleUnitaryData E K A n)

omit [NumberField E] [IsScalarTower E K A] [IsScalarTower ℚ E A] in
/-- This is exactly Kottwitz's division condition on the regular-module
commuting algebra, over the original rational base. -/
theorem isDivision_iff_regularCommutant :
    D.IsDivision ↔
      ∀ f : Langlands.Algebra.regularCommutant ℚ A, f ≠ 0 → IsUnit f :=
  Langlands.Algebra.regularCommutant_division_iff ℚ A

variable {Φ : (E →+* ℝ) → (K →+* ℂ)}
    (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)

/-- The actual chart-constructed Harris complex homomorphism factors through
the full commutant on the scalar-extended regular module. -/
def kottwitzPELCommutantHom :
    ℂ →ₐ[ℝ] Langlands.Algebra.regularCommutant ℝ (ℝ ⊗[ℚ] A) :=
  (D.realPositiveKottwitzHom C).val.rightRegularCommutant

/-- Its inclusion is the scalar restriction of the already constructed PEL
endomorphism, as an equality of actual operators. -/
theorem kottwitzPELCommutantHom_val (z : ℂ) :
    (D.kottwitzPELCommutantHom C z).val =
      (D.kottwitzPELHom C z).restrictScalars ℝ := rfl

@[simp] theorem kottwitzPELCommutantHom_apply (z : ℂ) (x : ℝ ⊗[ℚ] A) :
    (D.kottwitzPELCommutantHom C z).val x =
      x * (D.realPositiveKottwitzHom C).val.hom z := rfl

@[simp] theorem kottwitzPELCommutantHom_opposite (z : ℂ) :
    (Langlands.Algebra.regularOppositeEquivCommutant
      ℝ (ℝ ⊗[ℚ] A)).symm (D.kottwitzPELCommutantHom C z) =
        MulOpposite.op ((D.realPositiveKottwitzHom C).val.hom z) :=
  (D.realPositiveKottwitzHom C).val.rightRegularCommutant_opposite z

end Langlands.Shimura.CentralSimpleUnitaryData
