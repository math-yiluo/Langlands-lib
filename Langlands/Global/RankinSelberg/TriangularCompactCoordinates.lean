import Langlands.Global.RankinSelberg.TriangularDiagonal
import Langlands.Global.RankinSelberg.WhittakerSimpleRootSchwartzBound
import Langlands.Global.AdelicGLIwasawa

/-! # Diagonal coordinates of triangular standard-compact matrices -/

noncomputable section
universe u
open NumberField
open scoped Classical
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.GaugeDescent

open Langlands.GeneralLinear Unfolding

theorem norm_diagonal_of_triangular_unitary {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}
    (b : upperTriangularSubgroup n 𝕜)
    (hu : b.val.val ∈ Matrix.unitaryGroup (Fin n) 𝕜) (i : Fin n) :
    ‖b.val i i‖ = 1 := by
  have hi : (b.val⁻¹).val = star b.val.val :=
    Units.inv_eq_of_mul_eq_one_right (Matrix.mem_unitaryGroup_iff.mp hu)
  have h := congrArg norm (triangularDiagonal n 𝕜 b i).val_inv
  change ‖b.val i i * (b.val⁻¹) i i‖ = ‖(1 : 𝕜)‖ at h
  rw [hi, Matrix.star_apply, norm_mul, norm_star, norm_one] at h
  nlinarith [norm_nonneg (b.val i i)]

variable (F : Type u) [Field F] [NumberField F] {n : ℕ}

theorem triangularCompact_diagonal_real
    (b : upperTriangularSubgroup n (Adeles F))
    (hb : b.val ∈ PrimitiveAdelicHeight.standardCompact F n)
    (i : Fin n) (a : {v : InfinitePlace F // v.IsReal}) :
    ‖((rootArchUnit F (triangularDiagonal n (Adeles F) b i) :
      mixedEmbedding.mixedSpace F).1 a)‖ = 1 := by
  let φ := (PrimitiveAdelicHeight.realCoord a).comp
    ((InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp
      (RingHom.fst (InfiniteAdeles F) (FiniteAdeles F)))
  let b' : upperTriangularSubgroup n ℝ :=
    ⟨Matrix.GeneralLinearGroup.map φ b.val, b.property.map φ⟩
  have hu : b'.val.val ∈ Matrix.unitaryGroup (Fin n) ℝ :=
    ((mem_standardInfiniteCompact_iff F n (AdelicGL.infinite F n b.val)).mp hb.1).1 a
  exact norm_diagonal_of_triangular_unitary b' hu i

theorem triangularCompact_diagonal_complex
    (b : upperTriangularSubgroup n (Adeles F))
    (hb : b.val ∈ PrimitiveAdelicHeight.standardCompact F n)
    (i : Fin n) (a : {v : InfinitePlace F // v.IsComplex}) :
    ‖((rootArchUnit F (triangularDiagonal n (Adeles F) b i) :
      mixedEmbedding.mixedSpace F).2 a)‖ = 1 := by
  let φ := (PrimitiveAdelicHeight.complexCoord a).comp
    ((InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp
      (RingHom.fst (InfiniteAdeles F) (FiniteAdeles F)))
  let b' : upperTriangularSubgroup n ℂ :=
    ⟨Matrix.GeneralLinearGroup.map φ b.val, b.property.map φ⟩
  have hu : b'.val.val ∈ Matrix.unitaryGroup (Fin n) ℂ :=
    ((mem_standardInfiniteCompact_iff F n (AdelicGL.infinite F n b.val)).mp hb.1).2 a
  exact norm_diagonal_of_triangular_unitary b' hu i

theorem triangularCompact_diagonal_finite
    (b : upperTriangularSubgroup n (Adeles F))
    (hb : b.val ∈ PrimitiveAdelicHeight.standardCompact F n) (i : Fin n) :
    (rootFiniteUnit F (triangularDiagonal n (Adeles F) b i) : FiniteAdeles F) ∈
        integralFiniteAdeles F ∧
      (((rootFiniteUnit F (triangularDiagonal n (Adeles F) b i))⁻¹ :
        (FiniteAdeles F)ˣ) : FiniteAdeles F) ∈ integralFiniteAdeles F := by
  have h := (FiniteAdelicGL.mem_standardIntegral F n _).mp hb.2
  exact ⟨h.1 i i, fun v => by
    change ((AdelicGL.finite F n b.val)⁻¹ i i) v ∈ v.adicCompletionIntegers F
    exact h.2 i i v⟩

end Langlands.Global.RankinSelbergGlobal.GaugeDescent
