import Langlands.Global.ArchimedeanCompactTangentStatement
import Mathlib.Analysis.SpecialFunctions.Exponential

/-! # Compact curves from skew-adjoint matrix exponentials -/

noncomputable section

universe u

open scoped Classical Matrix.Norms.Operator
open NumberField

set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

private def realMatrixProjection (v : {v : InfinitePlace K // v.IsReal}) :
    ArchimedeanMatrix K n →⋆* Matrix (Fin n) (Fin n) ℝ :=
  { ((Pi.evalRingHom (fun _ : {v : InfinitePlace K // v.IsReal} => ℝ) v).comp
      (RingHom.fst _ _)).mapMatrix.toMonoidHom with
    map_star' := fun _ => rfl }

private def complexMatrixProjection (v : {v : InfinitePlace K // v.IsComplex}) :
    ArchimedeanMatrix K n →⋆* Matrix (Fin n) (Fin n) ℂ :=
  { ((Pi.evalRingHom (fun _ : {v : InfinitePlace K // v.IsComplex} => ℂ) v).comp
      (RingHom.snd _ _)).mapMatrix.toMonoidHom with
    map_star' := fun _ => rfl }

omit [NumberField K] in
private theorem coordinates_unitary_mem_compact (g : ArchimedeanGL K n)
    (hg : (g : ArchimedeanMatrix K n) ∈ unitary (ArchimedeanMatrix K n)) :
    (archimedeanGLCoordinates K n).symm g ∈ standardInfiniteCompact K n := by
  rw [mem_standardInfiniteCompact_iff, ContinuousMulEquiv.apply_symm_apply]
  exact ⟨fun v => Unitary.map_mem (realMatrixProjection K n v) hg,
    fun v => Unitary.map_mem (complexMatrixProjection K n v) hg⟩

set_option backward.isDefEq.respectTransparency false in
/-- Every actual compact matrix direction is realized by a compact exponential curve. -/
theorem compactTangentCurve (K : Type u) [Field K] [NumberField K] (n : ℕ) :
    CompactTangentCurveStatement K n := by
  intro X
  let A : ArchimedeanMatrix K n := realLieAlgebraToMatrix K n X
  have hA : star A = -A := X.property
  have hexp (t : ℝ) :
      NormedSpace.exp (t • A) ∈ unitary (ArchimedeanMatrix K n) := by
    apply NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
    change star (t • A) = -(t • A)
    simp [hA]
  let g : ℝ → ArchimedeanGL K n := fun t =>
    Unitary.toUnits ⟨NormedSpace.exp (t • A), hexp t⟩
  let c : ℝ → standardInfiniteCompact K n := fun t =>
    ⟨(archimedeanGLCoordinates K n).symm (g t),
      coordinates_unitary_mem_compact K n (g t) (hexp t)⟩
  refine ⟨c, ?_, ?_⟩
  · apply Subtype.ext
    apply (archimedeanGLCoordinates K n).injective
    change archimedeanGLCoordinates K n ((archimedeanGLCoordinates K n).symm (g 0)) =
      archimedeanGLCoordinates K n 1
    rw [ContinuousMulEquiv.apply_symm_apply, map_one]
    apply Units.ext
    simp [g]
  · have h : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • A)) A 0 := by
      simpa using hasDerivAt_exp_smul_const A (0 : ℝ)
    simpa only [c, ContinuousMulEquiv.apply_symm_apply, g, Unitary.val_toUnits_apply] using h

example : (K : Type u) → [Field K] → [NumberField K] → (n : ℕ) →
    CompactTangentCurveStatement K n :=
  @compactTangentCurve

end Langlands.Global.ArchimedeanGL
