import Langlands.BaseChange.SplitPlace
import Langlands.BaseChange.OrbitalIntegral
import Langlands.Representation.Archimedean.GeneralLinear
import Mathlib.MeasureTheory.Constructions.Pi

/-! # Matching at split infinite places and at a nonsplit real place -/

noncomputable section

universe u

open MeasureTheory
open scoped ContDiff Manifold Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.BaseChange

open Langlands.Archimedean

/-- A compactly supported smooth function on the real Lie group `GL_n(F)`. -/
def IsArchimedeanTest (F : Type u) [RCLike F] {n : ℕ} (f : GeneralLinear n F → ℂ) : Prop :=
  ContMDiff (matrixModel F n) 𝓘(ℝ, ℂ) ∞ f ∧ HasCompactSupport f

/-- Left and right finiteness for the standard orthogonal or unitary compact subgroup. -/
def IsBiFiniteArchimedeanTest (F : Type u) [RCLike F] {n : ℕ}
    (f : GeneralLinear n F → ℂ) : Prop :=
  IsArchimedeanTest F f ∧
    Module.Finite ℂ (Submodule.span ℂ (Set.range fun k : unitaryCompact F n =>
      fun g => f (k.val * g))) ∧
    Module.Finite ℂ (Submodule.span ℂ (Set.range fun k : unitaryCompact F n =>
      fun g => f (g * k.val)))

/-- Right-associated convolution in increasing factor order, starting at factor zero. -/
def archimedeanConvolutionProduct {G : Type u} [Group G] [MeasurableSpace G] (μ : Measure G) :
    {l : ℕ} → (Fin (l + 1) → G → ℂ) → G → ℂ
  | 0, f => f 0
  | l + 1, f => fun g => ∫ x, f 0 x * archimedeanConvolutionProduct μ (l := l) (Fin.tail f)
      (x⁻¹ * g) ∂μ

/-- The split ambient Haar measure maps to the measure of the ordered product of factors. -/
def IsArchimedeanSplitProductHaar {F : Type u} [RCLike F] {n l : ℕ}
    [MeasurableSpace (GeneralLinear n F)] [MeasurableSpace (GeneralLinear n (Fin l → F))]
    (μF : Measure (GeneralLinear n F)) (μE : Measure (GeneralLinear n (Fin l → F))) : Prop :=
  Measure.map (fun g i => Matrix.GeneralLinearGroup.map (Pi.evalRingHom (fun _ : Fin l => F) i) g)
    μE = Measure.pi fun _ : Fin l => μF

/-- At a split infinite place the cyclic tensor and its ordered convolution match for
product Haar measure. This includes `F = ℂ`, the infinite-place case over a totally
complex base. -/
def SplitArchimedeanMatchingStatement : Prop :=
  ∀ (F : Type u) [RCLike F] (n l : ℕ),
    letI : MeasurableSpace (GeneralLinear n F) := borel _
    letI : MeasurableSpace (GeneralLinear n (Fin (l + 1) → F)) := borel _
    haveI : BorelSpace (GeneralLinear n F) := ⟨rfl⟩
    haveI : BorelSpace (GeneralLinear n (Fin (l + 1) → F)) := ⟨rfl⟩
    ∀ (μF : Measure (GeneralLinear n F)) [μF.IsHaarMeasure],
      (∃ μE : Measure (GeneralLinear n (Fin (l + 1) → F)),
        μE.IsHaarMeasure ∧ IsArchimedeanSplitProductHaar μF μE) ∧
      ∀ μE : Measure (GeneralLinear n (Fin (l + 1) → F)), μE.IsHaarMeasure →
        IsArchimedeanSplitProductHaar μF μE →
        ∀ φ : Fin (l + 1) → GeneralLinear n F → ℂ,
          (∀ i, IsArchimedeanTest F (φ i)) →
          IsArchimedeanTest F (archimedeanConvolutionProduct μF φ) ∧
          ((∀ i, IsBiFiniteArchimedeanTest F (φ i)) →
            IsBiFiniteArchimedeanTest F (archimedeanConvolutionProduct μF φ)) ∧
          AreConcordant (splitCyclicShift F (l + 1)) (l + 1) μF μE
            (splitTensor φ) (archimedeanConvolutionProduct μF φ)

/-- Arthur–Clozel I.7.3 for the nonsplit extension `ℂ/ℝ` with the usual maximal compacts. -/
def NonsplitRealMatchingStatement : Prop :=
  ∀ n : ℕ,
    letI : MeasurableSpace (GeneralLinear n ℝ) := borel _
    letI : MeasurableSpace (GeneralLinear n ℂ) := borel _
    haveI : BorelSpace (GeneralLinear n ℝ) := ⟨rfl⟩
    haveI : BorelSpace (GeneralLinear n ℂ) := ⟨rfl⟩
    ∀ (μF : Measure (GeneralLinear n ℝ)) [μF.IsHaarMeasure]
      (μE : Measure (GeneralLinear n ℂ)) [μE.IsHaarMeasure],
      (∀ φ : GeneralLinear n ℂ → ℂ, IsBiFiniteArchimedeanTest ℂ φ →
        ∃ f : GeneralLinear n ℝ → ℂ, IsBiFiniteArchimedeanTest ℝ f ∧
          AreConcordant (RCLike.conjAe (K := ℂ)) 2 μF μE φ f) ∧
      ∀ f : GeneralLinear n ℝ → ℂ, IsBiFiniteArchimedeanTest ℝ f →
        VanishesOffNorms (RCLike.conjAe (K := ℂ)) 2 μF f →
        ∃ φ : GeneralLinear n ℂ → ℂ, IsBiFiniteArchimedeanTest ℂ φ ∧
          AreConcordant (RCLike.conjAe (K := ℂ)) 2 μF μE φ f

end Langlands.BaseChange
