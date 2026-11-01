import Langlands.Automorphic.SmoothArithmeticTransport
import Langlands.Automorphic.Growth
import Langlands.Global.ArchimedeanGrowthTransport

/-! # Arithmetic pullback on the actual adelic polynomial-growth spaces -/

noncomputable section
universe uK uL uM

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic.ContinuousRationalFunctions

open Langlands.Global AdelicGLTransport

variable {K : Type uK} {L : Type uL} {M : Type uM}
variable [Field K] [NumberField K] [Field L] [NumberField L] [Field M] [NumberField M]

/-- The constant on the slice at `b` comes from the old slice at its arithmetic image. -/
theorem arithmeticComap_hasPolynomialGrowth (n : ℕ) (e : K ≃+* L)
    {f : ContinuousRationalFunctions L n} (hf : HasPolynomialGrowth L n f) :
    HasPolynomialGrowth K n (arithmeticComap n e f) := by
  intro b
  have heq : infiniteSlice K n b (arithmeticComap n e f) =
      fun a => infiniteSlice L n (finiteEquiv n e b) f
        (Matrix.GeneralLinearGroup.map
          (AdelicFunctoriality.infiniteAdeleEquiv e).toRingHom a) := by
    funext a
    exact infiniteSlice_arithmeticComap n e b f a
  rw [heq]
  exact ArchimedeanGLTransport.hasPolynomialGrowth_arithmetic_map n e (hf _)

/-- Slice-dependent polynomial growth is preserved and reflected by actual pullback. -/
theorem arithmeticComap_hasPolynomialGrowth_iff (n : ℕ) (e : K ≃+* L)
    (f : ContinuousRationalFunctions L n) :
    HasPolynomialGrowth K n (arithmeticComap n e f) ↔ HasPolynomialGrowth L n f := by
  constructor
  · intro hf
    simpa only [arithmeticComap_symm_apply] using
      arithmeticComap_hasPolynomialGrowth n e.symm hf
  · exact arithmeticComap_hasPolynomialGrowth n e

theorem arithmeticComap_mem_polynomialGrowth_iff (n : ℕ) (e : K ≃+* L)
    (f : ContinuousRationalFunctions L n) :
    arithmeticComap n e f ∈ (polynomialGrowthSubrepresentation K n).toSubmodule ↔
      f ∈ (polynomialGrowthSubrepresentation L n).toSubmodule := by
  change arithmeticComap n e f ∈ polynomialGrowthSubrepresentation K n ↔
    f ∈ polynomialGrowthSubrepresentation L n
  rw [mem_polynomialGrowthSubrepresentation, mem_polynomialGrowthSubrepresentation]
  exact arithmeticComap_hasPolynomialGrowth_iff n e f

/-- Slice-wise real smoothness, finite local constancy and growth are reflected together. -/
theorem arithmeticComap_mem_smoothPolynomialGrowth_iff (n : ℕ) (e : K ≃+* L)
    (f : ContinuousRationalFunctions L n) :
    arithmeticComap n e f ∈ (smoothPolynomialGrowthSubrepresentation K n).toSubmodule ↔
      f ∈ (smoothPolynomialGrowthSubrepresentation L n).toSubmodule := by
  change
    (arithmeticComap n e f ∈ (smoothSubrepresentation K n).toSubmodule ∧
      arithmeticComap n e f ∈ (polynomialGrowthSubrepresentation K n).toSubmodule) ↔
    (f ∈ (smoothSubrepresentation L n).toSubmodule ∧
      f ∈ (polynomialGrowthSubrepresentation L n).toSubmodule)
  rw [arithmeticComap_mem_smooth_iff, arithmeticComap_mem_polynomialGrowth_iff]

/-- Real smoothness, a common open finite stabilizer and growth are reflected together. -/
theorem arithmeticComap_mem_finiteSmoothPolynomialGrowth_iff (n : ℕ) (e : K ≃+* L)
    (f : ContinuousRationalFunctions L n) :
    arithmeticComap n e f ∈
        (finiteSmoothPolynomialGrowthSubrepresentation K n).toSubmodule ↔
      f ∈ (finiteSmoothPolynomialGrowthSubrepresentation L n).toSubmodule := by
  change
    (arithmeticComap n e f ∈ (finiteSmoothRationalSubrepresentation K n).toSubmodule ∧
      arithmeticComap n e f ∈ (polynomialGrowthSubrepresentation K n).toSubmodule) ↔
    (f ∈ (finiteSmoothRationalSubrepresentation L n).toSubmodule ∧
      f ∈ (polynomialGrowthSubrepresentation L n).toSubmodule)
  rw [arithmeticComap_mem_finiteSmoothRational_iff, arithmeticComap_mem_polynomialGrowth_iff]

private theorem growthArithmeticComap_submodule_map (n : ℕ) (e : K ≃+* L)
    (P : Submodule ℂ (ContinuousRationalFunctions L n))
    (Q : Submodule ℂ (ContinuousRationalFunctions K n))
    (h : ∀ f, arithmeticComap n e f ∈ Q ↔ f ∈ P) :
    P.map (arithmeticComap n e) = Q := by
  ext f
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact (h g).mpr hg
  · intro hf
    obtain ⟨g, rfl⟩ := (arithmeticEquiv n e).surjective f
    exact ⟨g, (h g).mp hf, rfl⟩

/-- Continuous complex-linear arithmetic pullback on the existing growth subspaces. -/
def polynomialGrowthEquiv (n : ℕ) (e : K ≃+* L) :
    PolynomialGrowthRationalFunctions L n ≃L[ℂ] PolynomialGrowthRationalFunctions K n :=
  (arithmeticEquiv n e).ofSubmodules _ _
    (growthArithmeticComap_submodule_map n e _ _
      (arithmeticComap_mem_polynomialGrowth_iff n e))

@[simp] theorem evaluate_polynomialGrowthEquiv (n : ℕ) (e : K ≃+* L)
    (f : PolynomialGrowthRationalFunctions L n) (x : AdelicGL K n) :
    evaluate K n (polynomialGrowthEquiv n e f).val x =
      evaluate L n f.val (adelicEquiv n e x) := rfl

@[simp] theorem evaluate_polynomialGrowthEquiv_symm (n : ℕ) (e : K ≃+* L)
    (f : PolynomialGrowthRationalFunctions K n) (x : AdelicGL L n) :
    evaluate L n ((polynomialGrowthEquiv n e).symm f).val x =
      evaluate K n f.val (adelicEquiv n e.symm x) := rfl

@[simp] theorem polynomialGrowthEquiv_refl (n : ℕ)
    (f : PolynomialGrowthRationalFunctions K n) :
    polynomialGrowthEquiv n (RingEquiv.refl K) f = f := by
  apply Subtype.ext
  exact arithmeticComap_refl n f.val

theorem polynomialGrowthEquiv_trans (n : ℕ) (e : K ≃+* L) (a : L ≃+* M)
    (f : PolynomialGrowthRationalFunctions M n) :
    polynomialGrowthEquiv n (e.trans a) f =
      polynomialGrowthEquiv n e (polynomialGrowthEquiv n a f) := by
  apply Subtype.ext
  exact arithmeticComap_trans n e a f.val

@[simp] theorem polynomialGrowthEquiv_symm (n : ℕ) (e : K ≃+* L) :
    (polynomialGrowthEquiv n e).symm = polynomialGrowthEquiv n e.symm := by
  apply ContinuousLinearEquiv.ext
  funext f
  apply Subtype.ext
  rfl

theorem polynomialGrowthEquiv_rightAction (n : ℕ) (e : K ≃+* L)
    (g : AdelicGL K n) (f : PolynomialGrowthRationalFunctions L n) :
    polynomialGrowthEquiv n e (polynomialGrowthRightAction L n (adelicEquiv n e g) f) =
      polynomialGrowthRightAction K n g (polynomialGrowthEquiv n e f) := by
  apply Subtype.ext
  exact arithmeticComap_rightAction n e g f.val

/-- Pullback commutes with the faithful inclusion into ambient continuous functions. -/
theorem polynomialGrowthEquiv_inclusion (n : ℕ) (e : K ≃+* L)
    (f : PolynomialGrowthRationalFunctions L n) :
    arithmeticEquiv n e (polynomialGrowthInclusion L n f) =
      polynomialGrowthInclusion K n (polynomialGrowthEquiv n e f) := rfl

/-- Actual smooth polynomial-growth pullback, with inherited compact-open topology. -/
def smoothPolynomialGrowthEquiv (n : ℕ) (e : K ≃+* L) :
    (smoothPolynomialGrowthSubrepresentation L n).toSubmodule ≃L[ℂ]
      (smoothPolynomialGrowthSubrepresentation K n).toSubmodule :=
  (arithmeticEquiv n e).ofSubmodules _ _
    (growthArithmeticComap_submodule_map n e _ _
      (arithmeticComap_mem_smoothPolynomialGrowth_iff n e))

@[simp] theorem evaluate_smoothPolynomialGrowthEquiv (n : ℕ) (e : K ≃+* L)
    (f : (smoothPolynomialGrowthSubrepresentation L n).toSubmodule) (x : AdelicGL K n) :
    evaluate K n (smoothPolynomialGrowthEquiv n e f).val x =
      evaluate L n f.val (adelicEquiv n e x) := rfl

@[simp] theorem evaluate_smoothPolynomialGrowthEquiv_symm (n : ℕ) (e : K ≃+* L)
    (f : (smoothPolynomialGrowthSubrepresentation K n).toSubmodule) (x : AdelicGL L n) :
    evaluate L n ((smoothPolynomialGrowthEquiv n e).symm f).val x =
      evaluate K n f.val (adelicEquiv n e.symm x) := rfl

@[simp] theorem smoothPolynomialGrowthEquiv_refl (n : ℕ)
    (f : (smoothPolynomialGrowthSubrepresentation K n).toSubmodule) :
    smoothPolynomialGrowthEquiv n (RingEquiv.refl K) f = f := by
  apply Subtype.ext
  exact arithmeticComap_refl n f.val

theorem smoothPolynomialGrowthEquiv_trans (n : ℕ) (e : K ≃+* L) (a : L ≃+* M)
    (f : (smoothPolynomialGrowthSubrepresentation M n).toSubmodule) :
    smoothPolynomialGrowthEquiv n (e.trans a) f =
      smoothPolynomialGrowthEquiv n e (smoothPolynomialGrowthEquiv n a f) := by
  apply Subtype.ext
  exact arithmeticComap_trans n e a f.val

@[simp] theorem smoothPolynomialGrowthEquiv_symm (n : ℕ) (e : K ≃+* L) :
    (smoothPolynomialGrowthEquiv n e).symm = smoothPolynomialGrowthEquiv n e.symm := by
  apply ContinuousLinearEquiv.ext
  funext f
  apply Subtype.ext
  rfl

theorem smoothPolynomialGrowthEquiv_rightAction (n : ℕ) (e : K ≃+* L)
    (g : AdelicGL K n) (f : (smoothPolynomialGrowthSubrepresentation L n).toSubmodule) :
    smoothPolynomialGrowthEquiv n e
        ((smoothPolynomialGrowthSubrepresentation L n).toRepresentation (adelicEquiv n e g) f) =
      (smoothPolynomialGrowthSubrepresentation K n).toRepresentation g
        (smoothPolynomialGrowthEquiv n e f) := by
  apply Subtype.ext
  exact arithmeticComap_rightAction n e g f.val

/-- Actual growth-preserving pullback for smooth functions with a common finite stabilizer. -/
def finiteSmoothPolynomialGrowthEquiv (n : ℕ) (e : K ≃+* L) :
    (finiteSmoothPolynomialGrowthSubrepresentation L n).toSubmodule ≃L[ℂ]
      (finiteSmoothPolynomialGrowthSubrepresentation K n).toSubmodule :=
  (arithmeticEquiv n e).ofSubmodules _ _
    (growthArithmeticComap_submodule_map n e _ _
      (arithmeticComap_mem_finiteSmoothPolynomialGrowth_iff n e))

@[simp] theorem evaluate_finiteSmoothPolynomialGrowthEquiv (n : ℕ) (e : K ≃+* L)
    (f : (finiteSmoothPolynomialGrowthSubrepresentation L n).toSubmodule) (x : AdelicGL K n) :
    evaluate K n (finiteSmoothPolynomialGrowthEquiv n e f).val x =
      evaluate L n f.val (adelicEquiv n e x) := rfl

@[simp] theorem evaluate_finiteSmoothPolynomialGrowthEquiv_symm (n : ℕ) (e : K ≃+* L)
    (f : (finiteSmoothPolynomialGrowthSubrepresentation K n).toSubmodule) (x : AdelicGL L n) :
    evaluate L n ((finiteSmoothPolynomialGrowthEquiv n e).symm f).val x =
      evaluate K n f.val (adelicEquiv n e.symm x) := rfl

@[simp] theorem finiteSmoothPolynomialGrowthEquiv_refl (n : ℕ)
    (f : (finiteSmoothPolynomialGrowthSubrepresentation K n).toSubmodule) :
    finiteSmoothPolynomialGrowthEquiv n (RingEquiv.refl K) f = f := by
  apply Subtype.ext
  exact arithmeticComap_refl n f.val

theorem finiteSmoothPolynomialGrowthEquiv_trans (n : ℕ) (e : K ≃+* L) (a : L ≃+* M)
    (f : (finiteSmoothPolynomialGrowthSubrepresentation M n).toSubmodule) :
    finiteSmoothPolynomialGrowthEquiv n (e.trans a) f =
      finiteSmoothPolynomialGrowthEquiv n e (finiteSmoothPolynomialGrowthEquiv n a f) := by
  apply Subtype.ext
  exact arithmeticComap_trans n e a f.val

@[simp] theorem finiteSmoothPolynomialGrowthEquiv_symm (n : ℕ) (e : K ≃+* L) :
    (finiteSmoothPolynomialGrowthEquiv n e).symm =
      finiteSmoothPolynomialGrowthEquiv n e.symm := by
  apply ContinuousLinearEquiv.ext
  funext f
  apply Subtype.ext
  rfl

theorem finiteSmoothPolynomialGrowthEquiv_rightAction (n : ℕ) (e : K ≃+* L)
    (g : AdelicGL K n) (f : (finiteSmoothPolynomialGrowthSubrepresentation L n).toSubmodule) :
    finiteSmoothPolynomialGrowthEquiv n e
        ((finiteSmoothPolynomialGrowthSubrepresentation L n).toRepresentation
          (adelicEquiv n e g) f) =
      (finiteSmoothPolynomialGrowthSubrepresentation K n).toRepresentation g
        (finiteSmoothPolynomialGrowthEquiv n e f) := by
  apply Subtype.ext
  exact arithmeticComap_rightAction n e g f.val

/-- Compatibility with the existing inclusion from common stabilizers to smooth slices. -/
theorem smoothPolynomialGrowthEquiv_finiteSmoothInclusion (n : ℕ) (e : K ≃+* L)
    (f : (finiteSmoothPolynomialGrowthSubrepresentation L n).toSubmodule) :
    smoothPolynomialGrowthEquiv n e
        (Submodule.inclusion
          (finiteSmoothPolynomialGrowth_le_smoothPolynomialGrowth L n) f) =
      Submodule.inclusion (finiteSmoothPolynomialGrowth_le_smoothPolynomialGrowth K n)
        (finiteSmoothPolynomialGrowthEquiv n e f) := by
  apply Subtype.ext
  rfl

end Langlands.Automorphic.ContinuousRationalFunctions
