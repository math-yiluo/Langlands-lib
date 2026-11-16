import Langlands.Geometry.Analytic.FiniteMorphismFibres
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Isometric embeddings of algebraic extensions -/

noncomputable section

universe uK uE uF uL

namespace Langlands.Analytic

section NormUniqueness

variable {E : Type uE} {F : Type uF} {L : Type uL}
  [NormedField E] [IsUltrametricDist E] [CompleteSpace E]
  [NormedField F] [IsUltrametricDist F] [NormedAlgebra E F]
  [Algebra.IsAlgebraic E F] [NormedField L] [IsUltrametricDist L]

/-- A ring embedding of an algebraic extension that preserves the norm of the
complete base field is isometric on the whole extension. -/
theorem isometry_of_norm_on_algebraic_base (φ : F →+* L)
    (hφ : ∀ c : E, ‖φ (algebraMap E F c)‖ = ‖c‖) : Isometry φ := by
  have hna : IsNonarchimedean (pullbackAbsoluteValue φ) := by
    intro a b
    change ‖φ (a + b)‖ ≤ max ‖φ a‖ ‖φ b‖
    rw [map_add]
    exact IsUltrametricDist.norm_add_le_max _ _
  have hid : IsNonarchimedean (pullbackAbsoluteValue (RingHom.id F)) := by
    intro a b
    exact IsUltrametricDist.norm_add_le_max a b
  have hnorm := absoluteValue_eq_of_extends (F := E) (E := F)
    (pullbackAbsoluteValue φ) (pullbackAbsoluteValue (RingHom.id F))
    hna hid hφ (fun c => norm_algebraMap' F c)
  apply (AddMonoidHomClass.isometry_iff_norm φ).2
  intro a
  exact congrArg (fun v : AbsoluteValue F ℝ => v a) hnorm

/-- Algebra maps between normed extensions of a complete ultrametric field
are isometric when the source is algebraic. -/
theorem isometry_algHom_of_isAlgebraic [NormedAlgebra E L] (φ : F →ₐ[E] L) :
    Isometry φ :=
  isometry_of_norm_on_algebraic_base (E := E) φ.toRingHom fun c => by
    change ‖φ (algebraMap E F c)‖ = ‖c‖
    rw [φ.commutes, norm_algebraMap']

end NormUniqueness

section AlgebraicLift

variable (E : Type uE) (F : Type uF) (L : Type uL)
  [NormedField E] [IsUltrametricDist E] [CompleteSpace E]
  [NormedField F] [IsUltrametricDist F] [NormedAlgebra E F]
  [Algebra.IsAlgebraic E F] [NormedField L] [IsUltrametricDist L]
  [NormedAlgebra E L] [IsAlgClosed L]

/-- A chosen bounded embedding of an algebraic normed extension into an
algebraically closed normed extension of the same complete base. -/
def algebraicBoundedEmbedding : BoundedAlgHom E F L where
  toAlgHom := IsAlgClosed.lift
  bounded := ⟨1, zero_lt_one, fun a => by
    simpa using (isometry_algHom_of_isAlgebraic
      (IsAlgClosed.lift : F →ₐ[E] L)).norm_map_of_map_zero (map_zero _) a |>.le⟩

theorem isometry_algebraicBoundedEmbedding :
    Isometry (algebraicBoundedEmbedding E F L) :=
  isometry_algHom_of_isAlgebraic (IsAlgClosed.lift : F →ₐ[E] L)

end AlgebraicLift

section PrescribedEmbedding

variable {K : Type uK} {E : Type uE} {F : Type uF} {L : Type uL}
  [NormedField K] [NormedField E] [IsUltrametricDist E] [CompleteSpace E]
  [NormedField F] [IsUltrametricDist F] [NormedField L] [IsUltrametricDist L]
  [Algebra K E] [Algebra K F] [Algebra K L] [NormedAlgebra E F]
  [IsScalarTower K E F] [Algebra.IsAlgebraic E F] [IsAlgClosed L]

/-- Extend a prescribed isometric algebra map through an algebraic normed
extension, preserving its values and the norm. -/
theorem exists_isometric_algebraic_extension (i : E →ₐ[K] L) (hi : Isometry i) :
    ∃ j : BoundedAlgHom K F L, Isometry j ∧
      ∀ c : E, j (algebraMap E F c) = i c := by
  obtain ⟨j, hj⟩ := IsAlgClosed.surjective_domRestrict_of_isAlgebraic (E := F) i
  have hji : ∀ c : E, j (algebraMap E F c) = i c :=
    fun c => congrArg (fun f : E →ₐ[K] L => f c) hj
  have hjiso : Isometry j := isometry_of_norm_on_algebraic_base (E := E)
      j.toRingHom fun c => by
    change ‖j (algebraMap E F c)‖ = ‖c‖
    rw [hji]
    exact hi.norm_map_of_map_zero (map_zero _) c
  refine ⟨{ toAlgHom := j, bounded := ⟨1, zero_lt_one, fun a => ?_⟩ }, hjiso, hji⟩
  simpa using (hjiso.norm_map_of_map_zero (map_zero _) a).le

end PrescribedEmbedding

end Langlands.Analytic
