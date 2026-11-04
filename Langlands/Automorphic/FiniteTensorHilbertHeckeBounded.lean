import Langlands.Automorphic.FiniteTensorHilbertHecke
import Mathlib.Analysis.Normed.Operator.Basic

/-! # Bounded Hecke operators on full closed Hilbert-slice fixed spaces -/

noncomputable section
open scoped Classical TensorProduct
universe uF uV
set_option autoImplicit false
set_option maxHeartbeats 20000

namespace Langlands.TensorHilbertHeckeAux

open MeasureTheory

universe uG uH

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [MeasurableSpace G] [BorelSpace G]
variable (μ : Measure G) [μ.IsHaarMeasure]
variable (K : OpenSubgroup G) (hK : IsCompact (K : Set G))

/-- The sum of absolute values of the existing representation-independent
finite sample coefficients. This is a bound, not a claimed L1 norm identity. -/
def cornerSampleBound (f : Hecke.HeckeAlgebra.Corner μ K hK) : ℝ :=
  let t := Hecke.fixedLevelActionSamples μ K
    (Hecke.HeckeAlgebra.Corner.toHeckeAlgebra μ K hK f)
    (Hecke.HeckeAlgebra.Corner.rightInvariant μ K hK f)
  ∑ i, ‖t.coefficients i‖

theorem cornerSampleBound_nonneg (f : Hecke.HeckeAlgebra.Corner μ K hK) :
    0 ≤ cornerSampleBound μ K hK f :=
  Finset.sum_nonneg (fun _ _ => norm_nonneg _)

variable {H : Type uH} [NormedAddCommGroup H] [NormedSpace ℂ H]
variable (τ : Representation ℂ G H) (S : Subrepresentation τ)
variable (hτ : ∀ (g : G) (x : H), ‖τ g x‖ = ‖x‖)

include hτ

/-- The finite ambient formula bounds the entire fixed-space operator when
the original group operators preserve the ambient norm. -/
theorem cornerAction_norm_le (f : Hecke.HeckeAlgebra.Corner μ K hK)
    (x : fixedVectors S.toRepresentation K.toSubgroup) :
    ‖cornerAction τ S μ K hK f x‖ ≤ cornerSampleBound μ K hK f * ‖x‖ := by
  let t := Hecke.fixedLevelActionSamples μ K
    (Hecke.HeckeAlgebra.Corner.toHeckeAlgebra μ K hK f)
    (Hecke.HeckeAlgebra.Corner.rightInvariant μ K hK f)
  change ‖(cornerAction τ S μ K hK f x).val.val‖ ≤
    (∑ i, ‖t.coefficients i‖) * ‖x.val.val‖
  rw [cornerAction_eq_sum]
  calc
    ‖∑ i, t.coefficients i • τ (t.points i) x.val.val‖ ≤
        ∑ i, ‖t.coefficients i • τ (t.points i) x.val.val‖ := norm_sum_le _ _
    _ = (∑ i, ‖t.coefficients i‖) * ‖x.val.val‖ := by
      simp only [norm_smul, hτ, Finset.sum_mul]

/-- The same unital corner action, now with continuous bounded endomorphisms
of the full invariant-subspace fixed space and its inherited ambient norm. -/
def cornerContinuousAction :
    Hecke.HeckeAlgebra.Corner μ K hK →ₐ[ℂ]
      (fixedVectors S.toRepresentation K.toSubgroup →L[ℂ]
        fixedVectors S.toRepresentation K.toSubgroup) where
  toFun f := (cornerAction τ S μ K hK f).mkContinuous
    (cornerSampleBound μ K hK f) (cornerAction_norm_le μ K hK τ S hτ f)
  map_one' := by
    apply ContinuousLinearMap.ext
    intro x
    change cornerAction τ S μ K hK 1 x = x
    simp only [map_one, Module.End.one_apply]
  map_mul' f g := by
    apply ContinuousLinearMap.ext
    intro x
    change cornerAction τ S μ K hK (f * g) x =
      cornerAction τ S μ K hK f (cornerAction τ S μ K hK g x)
    simp only [map_mul, Module.End.mul_apply]
  map_zero' := by
    apply ContinuousLinearMap.ext
    intro x
    change cornerAction τ S μ K hK 0 x = 0
    simp only [map_zero, LinearMap.zero_apply]
  map_add' f g := by
    apply ContinuousLinearMap.ext
    intro x
    change cornerAction τ S μ K hK (f + g) x =
      cornerAction τ S μ K hK f x + cornerAction τ S μ K hK g x
    simp only [map_add, LinearMap.add_apply]
  commutes' c := by
    apply ContinuousLinearMap.ext
    intro x
    change cornerAction τ S μ K hK (algebraMap ℂ _ c) x =
      (algebraMap ℂ (Module.End ℂ _) c) x
    exact congrArg (fun T => T x) ((cornerAction τ S μ K hK).commutes c)

/-- Forgetting continuity recovers the unchanged algebraic operator. -/
theorem cornerContinuousAction_toLinearMap (f : Hecke.HeckeAlgebra.Corner μ K hK) :
    (cornerContinuousAction μ K hK τ S hτ f).toLinearMap =
      cornerAction τ S μ K hK f := rfl

/-- The continuous operator has the explicit representation-independent sample bound. -/
theorem cornerContinuousAction_norm_le (f : Hecke.HeckeAlgebra.Corner μ K hK) :
    ‖cornerContinuousAction μ K hK τ S hτ f‖ ≤ cornerSampleBound μ K hK f :=
  LinearMap.mkContinuous_norm_le _ (cornerSampleBound_nonneg μ K hK f)
    (cornerAction_norm_le μ K hK τ S hτ f)

end Langlands.TensorHilbertHeckeAux

namespace Langlands.Automorphic

open MeasureTheory
open Langlands.Global Langlands.Global.FiniteAdelicGL Langlands.RestrictedTensor

variable {F : Type uF} [Field F] [NumberField F] {n : ℕ}
variable {V : FinitePlace F → Type uV}
variable [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]

local instance tensorHilbertHeckeBoundedRationalGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance tensorHilbertHeckeBoundedContinuousGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance tensorHilbertHeckeBoundedSmoothGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance tensorHilbertHeckeBoundedFormsGroup :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance tensorHilbertHeckeBoundedFiniteSpaceGroup (S : FiniteRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _
local instance tensorHilbertHeckeBoundedLocalSpaceGroup (v : FinitePlace F)
    (L : LocalRealization F n v) : AddCommGroup L.Space := Submodule.addCommGroup _
local instance tensorHilbertHeckeBoundedMeasurable (v : FinitePlace F) :
    MeasurableSpace (FiniteLocalGL F n v) := borel _
local instance tensorHilbertHeckeBoundedBorel (v : FinitePlace F) :
    BorelSpace (FiniteLocalGL F n v) := ⟨rfl⟩

namespace FiniteTensorPresentation

variable {ρ : ∀ v, Representation ℂ (FiniteLocalGL F n v) (V v)}
variable {E : Finset (FinitePlace F)} {e : ∀ v, V v}
variable {he : ∀ v ∉ E, ∀ g ∈ localIntegral F n v, ρ v g (e v) = e v}
variable {S : FiniteRealization F n} (P : FiniteTensorPresentation F n ρ E e he S)
variable (b : Langlands.InvariantPositiveForm S.representation)

/-- The actual closed slice's full fixed space carries the same unital corner
action by bounded operators for its inherited global Hilbert norm. -/
def sliceHilbertContinuousCornerAction (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e)
    (μ : Measure (FiniteLocalGL F n v)) [μ.IsHaarMeasure]
    (K : OpenSubgroup (FiniteLocalGL F n v))
    (hK : IsCompact (K : Set (FiniteLocalGL F n v))) :=
  TensorHilbertHeckeAux.cornerContinuousAction μ K hK
    (b.completedRepresentation.comp (localInclusion F n v).toMonoidHom)
    (P.sliceHilbertRange b v y)
    (fun g x => b.completedRepresentation_norm (localInclusion F n v g) x)

end FiniteTensorPresentation
end Langlands.Automorphic
