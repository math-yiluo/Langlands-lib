import Langlands.Global.RankinSelberg.TriangularCompactCoordinates

/-! # Compatibility of simple-root Schwartz data on compact-factor fibers -/

noncomputable section
universe u
open NumberField
open scoped Classical
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.GaugeDescent

open Langlands.GeneralLinear Unfolding

private theorem norm_root_mul {𝕜 : Type*} [NormedField 𝕜]
    {I : Type*} [CommGroup I] (φ : I →* 𝕜ˣ) {r : ℕ}
    (d e : Fin (r + 1) → I)
    (he : ∀ j, ‖(φ (e j) : 𝕜)‖ = 1) (i : Fin r) :
    ‖(φ ((d * e) i.castSucc / (d * e) i.succ) : 𝕜)‖ =
      ‖(φ (d i.castSucc / d i.succ) : 𝕜)‖ := by
  simp only [Pi.mul_apply, map_mul, div_eq_mul_inv, mul_inv_rev, map_inv,
    Units.val_mul, Units.val_inv_eq_inv_val, norm_mul, norm_inv, he, inv_one,
    mul_one, one_mul]

private theorem mul_unit_mem_iff {A : Type*} [CommRing A] (O : Subring A)
    (x : A) (v : Aˣ) (hv : (v : A) ∈ O) (hvi : ((v⁻¹ : Aˣ) : A) ∈ O) :
    x * (v : A) ∈ O ↔ x ∈ O := by
  constructor
  · intro hx
    have h := O.mul_mem hx hvi
    simpa only [Units.mul_inv_cancel_right] using h
  · intro hx
    exact O.mul_mem hx hv

variable (F : Type u) [Field F] [NumberField F] {r : ℕ}

/-- The coordinate symmetries retained by the constructed majorant. -/
def HasSimpleRootCoordinateSymmetries (c : F) (Φ : RowVector F r → ℂ) : Prop :=
  ∀ x y,
    (∀ i a, ‖(archimedeanCoordinates F r x i).1 a‖ =
      ‖(archimedeanCoordinates F r y i).1 a‖) →
    (∀ i a, ‖(archimedeanCoordinates F r x i).2 a‖ =
      ‖(archimedeanCoordinates F r y i).2 a‖) →
    (∀ i, (algebraMap F (FiniteAdeles F) c * finiteCoordinates F r x i ∈
        integralFiniteAdeles F ↔
      algebraMap F (FiniteAdeles F) c * finiteCoordinates F r y i ∈
        integralFiniteAdeles F)) → Φ x = Φ y

/-- Coordinate-magnitude and integral-denominator symmetries imply invariance
under multiplication of the diagonal tuple by a triangular compact diagonal. -/
theorem schwartzRoot_mul_triangularCompact
    (c : F) (Φ : RowVector F r → ℂ)
    (hsymm : HasSimpleRootCoordinateSymmetries F c Φ)
    (d : Fin (r + 1) → Ideles F)
    (b : upperTriangularSubgroup (r + 1) (Adeles F))
    (hb : b.val ∈ PrimitiveAdelicHeight.standardCompact F (r + 1)) :
    Φ (gaugeSimpleRootRow F r (d * triangularDiagonal (r + 1) (Adeles F) b)) =
      Φ (gaugeSimpleRootRow F r d) := by
  let e := triangularDiagonal (r + 1) (Adeles F) b
  apply hsymm
  · intro i a
    let φ : Ideles F →* ℝˣ :=
      (Units.map (PrimitiveAdelicHeight.realCoord a).toMonoidHom).comp (rootArchUnit F)
    change ‖(φ ((d * e) i.castSucc / (d * e) i.succ) : ℝ)‖ =
      ‖(φ (d i.castSucc / d i.succ) : ℝ)‖
    exact norm_root_mul φ d e (fun j => triangularCompact_diagonal_real F b hb j a) i
  · intro i a
    let φ : Ideles F →* ℂˣ :=
      (Units.map (PrimitiveAdelicHeight.complexCoord a).toMonoidHom).comp (rootArchUnit F)
    change ‖(φ ((d * e) i.castSucc / (d * e) i.succ) : ℂ)‖ =
      ‖(φ (d i.castSucc / d i.succ) : ℂ)‖
    exact norm_root_mul φ d e (fun j => triangularCompact_diagonal_complex F b hb j a) i
  · intro i
    let v := rootFiniteUnit F (e i.castSucc / e i.succ)
    have hv : (v : FiniteAdeles F) ∈ integralFiniteAdeles F := by
      change (rootFiniteUnit F (e i.castSucc / e i.succ) : FiniteAdeles F) ∈ _
      rw [map_div, div_eq_mul_inv, Units.val_mul]
      exact (integralFiniteAdeles F).mul_mem
        (triangularCompact_diagonal_finite F b hb i.castSucc).1
        (triangularCompact_diagonal_finite F b hb i.succ).2
    have hvi : ((v⁻¹ : (FiniteAdeles F)ˣ) : FiniteAdeles F) ∈
        integralFiniteAdeles F := by
      change (((rootFiniteUnit F (e i.castSucc / e i.succ))⁻¹ :
        (FiniteAdeles F)ˣ) : FiniteAdeles F) ∈ _
      rw [map_div, inv_div, div_eq_mul_inv, Units.val_mul]
      exact (integralFiniteAdeles F).mul_mem
        (triangularCompact_diagonal_finite F b hb i.succ).1
        (triangularCompact_diagonal_finite F b hb i.castSucc).2
    have hrow : finiteCoordinates F r (gaugeSimpleRootRow F r (d * e)) i =
        finiteCoordinates F r (gaugeSimpleRootRow F r d) i * (v : FiniteAdeles F) := by
      change (rootFiniteUnit F ((d * e) i.castSucc / (d * e) i.succ) :
        FiniteAdeles F) = (rootFiniteUnit F (d i.castSucc / d i.succ) :
        FiniteAdeles F) * (v : FiniteAdeles F)
      rw [Pi.mul_apply, Pi.mul_apply, mul_div_mul_comm, map_mul, Units.val_mul]
    change algebraMap F (FiniteAdeles F) c *
        finiteCoordinates F r (gaugeSimpleRootRow F r (d * e)) i ∈ _ ↔ _
    rw [hrow, ← mul_assoc]
    exact mul_unit_mem_iff (integralFiniteAdeles F) _ v hv hvi

end Langlands.Global.RankinSelbergGlobal.GaugeDescent
