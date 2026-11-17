import Langlands.Automorphic.TransposeFiniteSmooth
import Langlands.Automorphic.Forms
import Langlands.Global.ArchimedeanTransposeCompact

/-! # Inverse-transpose pullback preserves actual automorphic forms -/

noncomputable section
universe u
open scoped Classical Matrix.Norms.Operator
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.ArchimedeanGL

open NumberField Langlands.GeneralLinear

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

/-- A uniform linear bound for the matrix/inverse height under inverse transpose. -/
theorem matrixHeight_inverseTranspose_le (g : InfiniteAdelicGL K n) :
    matrixHeight K n (inverseTranspose n (InfiniteAdeleRing K) g) ≤
      max 1 ‖(matrixTransposeLinear K n).toContinuousLinearMap‖ * matrixHeight K n g := by
  let c := max 1 ‖(matrixTransposeLinear K n).toContinuousLinearMap‖
  have hc : 1 ≤ c := le_max_left _ _
  have ht (a : ArchimedeanMatrix K n) : ‖a.transpose‖ ≤ c * ‖a‖ :=
    ((matrixTransposeLinear K n).toContinuousLinearMap.le_opNorm a).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg a))
  unfold matrixHeight
  rw [coordinates_inverseTranspose]
  change max 1
    (max ‖(archimedeanGLCoordinates K n g).inv.transpose‖
      ‖(archimedeanGLCoordinates K n g).val.transpose‖) ≤ c * matrixHeight K n g
  apply max_le
  · exact one_le_mul_of_one_le_of_one_le hc (one_le_matrixHeight K n g)
  · apply max_le
    · exact (ht _).trans (mul_le_mul_of_nonneg_left
        (norm_inv_le_matrixHeight K n g) (zero_le_one.trans hc))
    · exact (ht _).trans (mul_le_mul_of_nonneg_left
        (norm_val_le_matrixHeight K n g) (zero_le_one.trans hc))

/-- Polynomial growth pulls back along the actual inverse-transpose automorphism. -/
theorem HasPolynomialGrowth.transpose {f : InfiniteAdelicGL K n → ℂ}
    (hf : HasPolynomialGrowth K n f) :
    HasPolynomialGrowth K n
      (fun g => f (inverseTranspose n (InfiniteAdeleRing K) g)) := by
  obtain ⟨C, hC, d, hf⟩ := hf
  let c := max 1 ‖(matrixTransposeLinear K n).toContinuousLinearMap‖
  have hc : 0 ≤ c := zero_le_one.trans (le_max_left _ _)
  refine ⟨C * c ^ d, mul_nonneg hC (pow_nonneg hc d), d, ?_⟩
  intro g
  calc
    ‖f (inverseTranspose n (InfiniteAdeleRing K) g)‖ ≤
        C * matrixHeight K n (inverseTranspose n (InfiniteAdeleRing K) g) ^ d := hf _
    _ ≤ C * (c * matrixHeight K n g) ^ d :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀
        (matrixHeight_nonneg K n _) (matrixHeight_inverseTranspose_le K n g) d) hC
    _ = (C * c ^ d) * matrixHeight K n g ^ d := by rw [mul_pow, mul_assoc]

end Langlands.Global.ArchimedeanGL

namespace Langlands.Automorphic

open Langlands.Global Langlands.GeneralLinear NumberField IsDedekindDomain
open ContinuousRationalFunctions

set_option backward.isDefEq.respectTransparency false

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

local instance transposeAutomorphicRationalGroup :
    AddCommGroup (RationalInvariantFunctions K n) := Submodule.addCommGroup _
local instance transposeAutomorphicContinuousGroup :
    AddCommGroup (ContinuousRationalFunctions K n) := Submodule.addCommGroup _
local instance transposeAutomorphicFiniteSmoothGroup :
    AddCommGroup (FiniteSmoothRationalFunctions K n) := Submodule.addCommGroup _
local instance transposeAutomorphicFormGroup :
    AddCommGroup (AutomorphicForms K n) := Submodule.addCommGroup _

/-- Growth is checked at the reindexed finite slice using one uniform height bound. -/
theorem hasPolynomialGrowth_continuousTranspose {f : ContinuousRationalFunctions K n}
    (hf : HasPolynomialGrowth K n f) :
    HasPolynomialGrowth K n (continuousTranspose K n f) := by
  intro b
  rw [infiniteSlice_continuousTranspose]
  exact (hf (inverseTranspose n (FiniteAdeleRing (𝓞 K) K) b)).transpose K n

@[simp]
theorem hasPolynomialGrowth_continuousTranspose_iff (f : ContinuousRationalFunctions K n) :
    HasPolynomialGrowth K n (continuousTranspose K n f) ↔ HasPolynomialGrowth K n f := by
  constructor
  · intro hf
    simpa only [continuousTranspose_involutive] using
      hasPolynomialGrowth_continuousTranspose K n hf
  · exact hasPolynomialGrowth_continuousTranspose K n

/-- The whole compact orbit on actual adelic functions is transported by pullback. -/
theorem infiniteOrbitSpan_continuousTranspose (f : ContinuousRationalFunctions K n) :
    (infiniteOrbitSpan K n (standardInfiniteCompact K n) f).map
        (continuousTranspose K n).toLinearMap =
      infiniteOrbitSpan K n (standardInfiniteCompact K n) (continuousTranspose K n f) := by
  unfold infiniteOrbitSpan
  rw [Submodule.map_span, ← Set.range_comp]
  apply congrArg (Submodule.span ℂ)
  apply Set.Subset.antisymm
  · rintro _ ⟨k, rfl⟩
    refine ⟨ArchimedeanGL.compactTranspose K n k, ?_⟩
    simpa only [Function.comp_apply, LinearEquiv.coe_toLinearMap,
      Langlands.Global.RankinSelbergGlobal.Unfolding.inverseTranspose_ofInfinite,
      ArchimedeanGL.compactTranspose_val] using
      (continuousTranspose_rightAction K n (AdelicGL.ofInfinite K n k.val) f).symm
  · rintro _ ⟨k, rfl⟩
    refine ⟨ArchimedeanGL.compactTranspose K n k, ?_⟩
    simpa only [Function.comp_apply, LinearEquiv.coe_toLinearMap,
      Langlands.Global.RankinSelbergGlobal.Unfolding.inverseTranspose_ofInfinite,
      ArchimedeanGL.compactTranspose_val, inverseTranspose_involutive] using
      continuousTranspose_rightAction K n
        (AdelicGL.ofInfinite K n
          (inverseTranspose n (InfiniteAdeleRing K) k.val)) f

/-- The common compact orbit, rather than separate slice orbits, remains finite. -/
theorem isStandardInfiniteFinite_continuousTranspose_iff
    (f : ContinuousRationalFunctions K n) :
    IsInfiniteFinite K n (standardInfiniteCompact K n) (continuousTranspose K n f) ↔
      IsInfiniteFinite K n (standardInfiniteCompact K n) f := by
  let e := (continuousTranspose K n).ofSubmodules _ _
    (infiniteOrbitSpan_continuousTranspose K n f)
  exact (LinearMap.finite_iff_of_bijective e.toLinearMap e.bijective).symm

/-- All four actual automorphic conditions are preserved and reflected by pullback. -/
theorem finiteSmoothTranspose_mem_automorphic_iff (f : FiniteSmoothRationalFunctions K n) :
    finiteSmoothTranspose K n f ∈ automorphicSubrepresentation K n ↔
      f ∈ automorphicSubrepresentation K n := by
  rw [mem_automorphicSubrepresentation, mem_automorphicSubrepresentation]
  unfold IsAutomorphicForm
  exact and_congr (hasFiniteLevel_continuousTranspose_iff K n f.val)
    (and_congr (isStandardInfiniteFinite_continuousTranspose_iff K n f.val)
      (and_congr (isCenterFinite_finiteSmoothTranspose_iff K n f)
        (hasPolynomialGrowth_continuousTranspose_iff K n f.val)))

private theorem automorphicSubrepresentation_map_transpose :
    (automorphicSubrepresentation K n).toSubmodule.map
        (finiteSmoothTranspose K n).toLinearMap =
      (automorphicSubrepresentation K n).toSubmodule := by
  ext f
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact (finiteSmoothTranspose_mem_automorphic_iff K n g).mpr hg
  · intro hf
    obtain ⟨g, rfl⟩ := (finiteSmoothTranspose K n).surjective f
    exact ⟨g, (finiteSmoothTranspose_mem_automorphic_iff K n g).mp hf, rfl⟩

namespace AutomorphicForms

/-- Inverse-transpose argument pullback on the existing space of actual forms. -/
def transpose : AutomorphicForms K n ≃ₗ[ℂ] AutomorphicForms K n :=
  (finiteSmoothTranspose K n).ofSubmodules _ _
    (automorphicSubrepresentation_map_transpose K n)

@[simp]
theorem transpose_val (f : AutomorphicForms K n) :
    (transpose K n f).val = finiteSmoothTranspose K n f.val := rfl

@[simp]
theorem toContinuous_transpose (f : AutomorphicForms K n) :
    automorphicToContinuous K n (transpose K n f) =
      continuousTranspose K n (automorphicToContinuous K n f) := rfl

@[simp]
theorem transpose_involutive (f : AutomorphicForms K n) :
    transpose K n (transpose K n f) = f :=
  Subtype.ext (finiteSmoothTranspose_involutive K n f.val)

@[simp]
theorem evaluate_transpose (f : AutomorphicForms K n) (g : AdelicGL K n) :
    evaluate K n (automorphicToContinuous K n (transpose K n f)) g =
      evaluate K n (automorphicToContinuous K n f)
        (inverseTranspose n (AdeleRing (𝓞 K) K) g) := rfl

/-- The finite action retains the actual inverse-transpose covariance. -/
theorem transpose_finiteRightAction (d : FiniteAdelicGL K n) (f : AutomorphicForms K n) :
    transpose K n
        (automorphicFiniteRightAction K n (inverseTranspose n (FiniteAdeleRing (𝓞 K) K) d) f) =
      automorphicFiniteRightAction K n d (transpose K n f) := by
  apply Subtype.ext
  exact finiteSmoothTranspose_finiteRightAction K n d f.val

end AutomorphicForms
end Langlands.Automorphic
