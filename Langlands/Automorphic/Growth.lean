import Langlands.Global.ArchimedeanGrowth
import Langlands.Automorphic.Smooth

noncomputable section
universe u

namespace Langlands.Automorphic

open Langlands.Global ContinuousRationalFunctions

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

/-- Each fixed finite-adelic slice has polynomial growth in the actual infinite matrix
and its inverse. The constant and exponent may depend on the finite slice. -/
def HasPolynomialGrowth (f : ContinuousRationalFunctions K n) : Prop :=
  ∀ b : FiniteAdelicGL K n,
    ArchimedeanGL.HasPolynomialGrowth K n (infiniteSlice K n b f)

/-- Actual polynomial-growth rational functions, stable under full adelic translation. -/
def polynomialGrowthSubrepresentation : Subrepresentation (continuousRightAction K n) where
  toSubmodule := ⨅ b : FiniteAdelicGL K n,
    (ArchimedeanGL.polynomialGrowthFunctions K n).comap (infiniteSlice K n b)
  apply_mem_toSubmodule g f hf := by
    simp only [Submodule.mem_iInf, Submodule.mem_comap,
      ArchimedeanGL.mem_polynomialGrowthFunctions] at hf ⊢
    intro b
    have h := (hf (b * AdelicGL.finite K n g)).rightTranslate
      (AdelicGL.infinite K n g)
    change ArchimedeanGL.HasPolynomialGrowth K n
      (fun a => evaluate K n f (AdelicGL.pair K n
        (a * AdelicGL.infinite K n g) (b * AdelicGL.finite K n g))) at h
    change ArchimedeanGL.HasPolynomialGrowth K n
      (fun a => evaluate K n f (AdelicGL.pair K n a b * g))
    simpa only [AdelicGL.pair_mul_right] using h

@[simp]
theorem mem_polynomialGrowthSubrepresentation (f : ContinuousRationalFunctions K n) :
    f ∈ polynomialGrowthSubrepresentation K n ↔ HasPolynomialGrowth K n f := by
  change f ∈ (⨅ b : FiniteAdelicGL K n,
    (ArchimedeanGL.polynomialGrowthFunctions K n).comap (infiniteSlice K n b) :
      Submodule ℂ _) ↔ _
  simp only [Submodule.mem_iInf, Submodule.mem_comap,
    ArchimedeanGL.mem_polynomialGrowthFunctions, HasPolynomialGrowth]

abbrev PolynomialGrowthRationalFunctions := (polynomialGrowthSubrepresentation K n).toSubmodule

def polynomialGrowthRightAction :
    Representation ℂ (AdelicGL K n) (PolynomialGrowthRationalFunctions K n) :=
  (polynomialGrowthSubrepresentation K n).toRepresentation

/-- The actual faithful realization in continuous rational-invariant functions. -/
def polynomialGrowthInclusion :
    (polynomialGrowthRightAction K n).IntertwiningMap (continuousRightAction K n) where
  toLinearMap := (polynomialGrowthSubrepresentation K n).toSubmodule.subtype
  isIntertwining' _ := by ext; rfl

theorem polynomialGrowthInclusion_injective :
    Function.Injective (polynomialGrowthInclusion K n) := Subtype.val_injective

@[simp]
theorem evaluate_polynomialGrowthRightAction (g x : AdelicGL K n)
    (f : PolynomialGrowthRationalFunctions K n) :
    evaluate K n (polynomialGrowthRightAction K n g f).val x =
      evaluate K n f.val (x * g) := rfl

/-- Slice-wise smoothness and actual polynomial growth together. -/
def smoothPolynomialGrowthSubrepresentation : Subrepresentation (continuousRightAction K n) :=
  smoothSubrepresentation K n ⊓ polynomialGrowthSubrepresentation K n

/-- Real-smooth polynomial-growth functions with a common open finite stabilizer. -/
def finiteSmoothPolynomialGrowthSubrepresentation :
    Subrepresentation (continuousRightAction K n) :=
  finiteSmoothRationalSubrepresentation K n ⊓ polynomialGrowthSubrepresentation K n

theorem finiteSmoothPolynomialGrowth_le_smoothPolynomialGrowth :
    finiteSmoothPolynomialGrowthSubrepresentation K n ≤
      smoothPolynomialGrowthSubrepresentation K n :=
  inf_le_inf_right _ (finiteSmoothRational_le_smooth K n)

end Langlands.Automorphic
