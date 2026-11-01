import Langlands.HarmonicAnalysis.VectorTestFunction
import Langlands.Representation.Hecke.TestFunction
import Mathlib.Algebra.Algebra.NonUnitalSubalgebra

/-!
# The pointwise test-function algebra and its smooth multipliers

Renard (9 July 2026), II.2.4–II.2.5, printed pp.38–39 / PDF44–45.
This packaging is separate from the Hecke convolution algebra.
-/

noncomputable section

namespace Langlands.HarmonicAnalysis.PointwiseTestAlgebra

universe uX

variable (X : Type uX) [TopologicalSpace X]

/-- Compactly supported locally constant functions, as a pointwise nonunital subalgebra. -/
def compactlySupportedSubalgebra : NonUnitalSubalgebra ℂ (LocallyConstant X ℂ) where
  toSubmodule := VectorTestFunction.compactlySupportedSubmodule X ℂ
  mul_mem' hf _ := hf.mul_right

/-- Renard's pointwise complex algebra `D(X)` with its inherited structures. -/
abbrev Carrier := ↥(compactlySupportedSubalgebra X)

instance : CoeFun (Carrier X) (fun _ => X → ℂ) := ⟨fun f => f.1⟩

variable {X}

@[simp]
theorem mem_compactlySupportedSubalgebra (f : LocallyConstant X ℂ) :
    f ∈ compactlySupportedSubalgebra X ↔ HasCompactSupport (f : X → ℂ) := Iff.rfl

@[ext]
theorem ext {f g : Carrier X} (h : ∀ x, f x = g x) : f = g :=
  Subtype.ext (LocallyConstant.ext h)

theorem locallyConstant (f : Carrier X) : IsLocallyConstant (f : X → ℂ) :=
  f.1.isLocallyConstant

theorem hasCompactSupport (f : Carrier X) : HasCompactSupport (f : X → ℂ) := f.2

@[simp]
theorem zero_apply (x : X) : (0 : Carrier X) x = 0 := rfl

@[simp]
theorem add_apply (f g : Carrier X) (x : X) : (f + g) x = f x + g x := rfl

@[simp]
theorem neg_apply (f : Carrier X) (x : X) : (-f) x = -f x := rfl

@[simp]
theorem sub_apply (f g : Carrier X) (x : X) : (f - g) x = f x - g x := rfl

@[simp]
theorem smul_apply (c : ℂ) (f : Carrier X) (x : X) : (c • f) x = c • f x := rfl

@[simp]
theorem mul_apply (f g : Carrier X) (x : X) : (f * g) x = f x * g x := rfl

/-- The actual faithful inclusion into the ambient pointwise algebra. -/
def inclusion : Carrier X →ₙₐ[ℂ] LocallyConstant X ℂ :=
  NonUnitalSubalgebraClass.subtype (compactlySupportedSubalgebra X)

@[simp]
theorem inclusion_apply (f : Carrier X) (x : X) : inclusion f x = f x := rfl

theorem inclusion_injective : Function.Injective (inclusion (X := X)) :=
  Subtype.coe_injective

/-- Identity on functions, comparing the algebra carrier to the published vector carrier. -/
def vectorEquiv : Carrier X ≃ₗ[ℂ] VectorTestFunction.Space X ℂ :=
  (compactlySupportedSubalgebra X).toSubmoduleEquiv.symm

@[simp]
theorem vectorEquiv_apply (f : Carrier X) (x : X) : vectorEquiv f x = f x := rfl

@[simp]
theorem vectorEquiv_symm_apply (f : VectorTestFunction.Space X ℂ) (x : X) :
    vectorEquiv.symm f x = f x := rfl

/-- Identity on functions, comparing pointwise tests to the original scalar tests. -/
def scalarEquiv : Carrier X ≃ₗ[ℂ] SchwartzBruhat X :=
  vectorEquiv.trans VectorTestFunction.scalarEquiv.symm

@[simp]
theorem scalarEquiv_apply (f : Carrier X) (x : X) : scalarEquiv f x = f x := rfl

@[simp]
theorem scalarEquiv_symm_apply (f : SchwartzBruhat X) (x : X) :
    scalarEquiv.symm f x = f x := rfl

theorem isClopen_support (f : Carrier X) : IsClopen (Function.support f) :=
  Hecke.TestFunction.isClopen_support (scalarEquiv f)

theorem isCompact_support (f : Carrier X) : IsCompact (Function.support f) :=
  Hecke.TestFunction.isCompact_support (scalarEquiv f)

theorem tsupport_eq_support (f : Carrier X) :
    tsupport (f : X → ℂ) = Function.support f :=
  Hecke.TestFunction.tsupport_eq_support (scalarEquiv f)

/-- Ambient smooth functions act by multiplication; compact support comes from the test. -/
instance ambientModule : Module (LocallyConstant X ℂ) (Carrier X) where
  smul g f := ⟨g * f.1, f.2.mul_left⟩
  one_smul f := by ext x; exact one_mul (f x)
  mul_smul g h f := by ext x; exact mul_assoc (g x) (h x) (f x)
  smul_zero g := by ext x; exact mul_zero (g x)
  smul_add g f h := by ext x; exact mul_add (g x) (f x) (h x)
  add_smul g h f := by ext x; exact add_mul (g x) (h x) (f x)
  zero_smul f := by ext x; exact zero_mul (f x)

@[simp]
theorem ambient_smul_apply (g : LocallyConstant X ℂ) (f : Carrier X) (x : X) :
    (g • f) x = g x * f x := rfl

@[simp]
theorem inclusion_ambient_smul (g : LocallyConstant X ℂ) (f : Carrier X) :
    inclusion (g • f) = g * inclusion f := rfl

@[simp]
theorem inclusion_smul (g f : Carrier X) : inclusion g • f = g * f := rfl

instance ambientScalarTower : IsScalarTower ℂ (LocallyConstant X ℂ) (Carrier X) where
  smul_assoc c g f := by
    ext x
    exact mul_assoc c (g x) (f x)

instance ambientSMulCommClass : SMulCommClass ℂ (LocallyConstant X ℂ) (Carrier X) where
  smul_comm c g f := by
    ext x
    exact mul_left_comm c (g x) (f x)

@[simp]
theorem const_smul (c : ℂ) (f : Carrier X) : LocallyConstant.const X c • f = c • f := rfl

/-- Each ambient smooth multiplier is a genuine complex-linear endomorphism. -/
def multiplier (g : LocallyConstant X ℂ) : Module.End ℂ (Carrier X) where
  toFun f := g • f
  map_add' := smul_add g
  map_smul' c f := by
    ext x
    exact mul_left_comm (g x) c (f x)

@[simp]
theorem multiplier_apply (g : LocallyConstant X ℂ) (f : Carrier X) :
    multiplier g f = g • f := rfl

@[simp]
theorem multiplier_one : multiplier (1 : LocallyConstant X ℂ) = 1 := by
  ext f x
  exact one_mul (f x)

theorem multiplier_mul (g h : LocallyConstant X ℂ) :
    multiplier (g * h) = multiplier g * multiplier h := by
  ext f x
  exact mul_assoc (g x) (h x) (f x)

theorem multiplier_add (g h : LocallyConstant X ℂ) :
    multiplier (g + h) = multiplier g + multiplier h := by
  ext f x
  exact add_mul (g x) (h x) (f x)

theorem multiplier_smul (c : ℂ) (g : LocallyConstant X ℂ) :
    multiplier (c • g) = c • multiplier g := by
  ext f x
  exact mul_assoc c (g x) (f x)

end Langlands.HarmonicAnalysis.PointwiseTestAlgebra
