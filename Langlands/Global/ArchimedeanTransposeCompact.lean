import Langlands.Global.ArchimedeanTransposeSmooth
import Langlands.Global.ArchimedeanCompact

/-! # Transpose inverse preserves the actual standard archimedean compact subgroup -/

noncomputable section
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.ArchimedeanGL

open NumberField Langlands.GeneralLinear

variable (F : Type u) [Field F] (n : ℕ)

/-- Orthogonality and unitarity are preserved by transpose inverse. -/
theorem inverseTranspose_mem_standardInfiniteCompact
    {g : Matrix.GeneralLinearGroup (Fin n) (InfiniteAdeleRing F)}
    (hg : g ∈ standardInfiniteCompact F n) :
    inverseTranspose n (InfiniteAdeleRing F) g ∈ standardInfiniteCompact F n := by
  have hi := (mem_standardInfiniteCompact_iff F n g⁻¹).mp
    ((standardInfiniteCompact F n).inv_mem hg)
  rw [mem_standardInfiniteCompact_iff, coordinates_inverseTranspose]
  constructor
  · intro v
    change (realMatrix F n ((archimedeanGLCoordinates F n g)⁻¹) v).transpose ∈
      Matrix.unitaryGroup (Fin n) ℝ
    rw [← map_inv]
    exact Matrix.transpose_mem_unitaryGroup_iff.mpr (hi.1 v)
  · intro v
    change (complexMatrix F n ((archimedeanGLCoordinates F n g)⁻¹) v).transpose ∈
      Matrix.unitaryGroup (Fin n) ℂ
    rw [← map_inv]
    exact Matrix.transpose_mem_unitaryGroup_iff.mpr (hi.2 v)

/-- Transpose inverse restricts to a continuous involution of the actual compact group. -/
def compactTranspose : standardInfiniteCompact F n ≃ₜ* standardInfiniteCompact F n where
  toFun k := ⟨inverseTranspose n (InfiniteAdeleRing F) k.val,
    inverseTranspose_mem_standardInfiniteCompact F n k.property⟩
  invFun k := ⟨inverseTranspose n (InfiniteAdeleRing F) k.val,
    inverseTranspose_mem_standardInfiniteCompact F n k.property⟩
  left_inv k := Subtype.ext (inverseTranspose_involutive n _ k.val)
  right_inv k := Subtype.ext (inverseTranspose_involutive n _ k.val)
  map_mul' k l := Subtype.ext (map_mul (inverseTranspose n (InfiniteAdeleRing F)) k.val l.val)
  continuous_toFun := ((continuous_inverseTranspose n _).comp continuous_subtype_val).subtype_mk _
  continuous_invFun := ((continuous_inverseTranspose n _).comp continuous_subtype_val).subtype_mk _

@[simp]
theorem compactTranspose_val (k : standardInfiniteCompact F n) :
    (compactTranspose F n k).val = inverseTranspose n (InfiniteAdeleRing F) k.val := rfl

@[simp]
theorem compactTranspose_involutive (k : standardInfiniteCompact F n) :
    compactTranspose F n (compactTranspose F n k) = k :=
  Subtype.ext (inverseTranspose_involutive n _ k.val)

variable [NumberField F]

/-- Pullback transports the entire orbit span for the actual standard compact group. -/
theorem compactOrbitSpan_smoothTranspose (f : SmoothFunctions F n) :
    Langlands.FiniteVectors.orbitSpan
        ((smoothRightAction F n).comp (standardInfiniteCompact F n).subtype)
        (smoothTranspose F n f) =
      (Langlands.FiniteVectors.orbitSpan
        ((smoothRightAction F n).comp (standardInfiniteCompact F n).subtype) f).map
        (smoothTranspose F n).toLinearMap := by
  unfold Langlands.FiniteVectors.orbitSpan
  rw [Submodule.map_span, ← Set.range_comp]
  apply congrArg (Submodule.span ℂ)
  apply Set.Subset.antisymm
  · rintro _ ⟨k, rfl⟩
    refine ⟨compactTranspose F n k, ?_⟩
    exact smoothTranspose_smoothRightAction F n k.val f
  · rintro _ ⟨k, rfl⟩
    refine ⟨compactTranspose F n k, ?_⟩
    exact (smoothTranspose_smoothRightAction F n
      (inverseTranspose n (InfiniteAdeleRing F) k.val) f).symm

/-- Transpose inverse preserves and reflects actual compact finiteness. -/
theorem isCompactFinite_smoothTranspose_iff (f : SmoothFunctions F n) :
    Langlands.FiniteVectors.IsFiniteVector
      ((smoothRightAction F n).comp (standardInfiniteCompact F n).subtype)
      (smoothTranspose F n f) ↔
    Langlands.FiniteVectors.IsFiniteVector
      ((smoothRightAction F n).comp (standardInfiniteCompact F n).subtype) f := by
  let e := (smoothTranspose F n).ofSubmodules _ _
    (compactOrbitSpan_smoothTranspose F n f).symm
  exact (LinearMap.finite_iff_of_bijective e.toLinearMap e.bijective).symm

end Langlands.Global.ArchimedeanGL
