import Langlands.Global.LocalModularCharacter.HaarScaleNorm

/-! # Place-level glue for the local modular-character formula -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped NNReal

namespace Langlands.Global

section RealStructure

/-- A normed field that is isometrically isomorphic, as a ring, to a finite-dimensional real
normed algebra which is a normed field carries a finite-dimensional real normed space
structure. -/
theorem exists_normedSpace_real_of_ringEquiv {E V : Type*} [NormedField E] [NormedField V]
    [NormedAlgebra ℝ V] [FiniteDimensional ℝ V] (e : E ≃+* V) (he : ∀ x, ‖e x‖ = ‖x‖) :
    ∃ _ : NormedSpace ℝ E, FiniteDimensional ℝ E := by
  let _ : Algebra ℝ E := (e.symm.toRingHom.comp (algebraMap ℝ V)).toAlgebra
  have hsmul (r : ℝ) (x : E) : e (r • x) = r • e x := by
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, RingHom.algebraMap_toAlgebra,
      RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, RingEquiv.apply_symm_apply]
  let _ : NormedSpace ℝ E :=
    { toModule := inferInstance
      norm_smul_le := fun r x => by rw [← he, hsmul, norm_smul, he] }
  let eL : E ≃ₗ[ℝ] V := { e.toAddEquiv with map_smul' := hsmul }
  exact ⟨inferInstance, LinearEquiv.finiteDimensional eL.symm⟩

/-- The completion at an infinite place is a finite-dimensional real normed space for its
existing norm. -/
theorem exists_normedSpace_real_infiniteCompletion {F : Type u} [Field F]
    (w : InfinitePlace F) : ∃ _ : NormedSpace ℝ w.Completion, FiniteDimensional ℝ w.Completion := by
  rcases w.isReal_or_isComplex with hw | hw
  · refine exists_normedSpace_real_of_ringEquiv (InfinitePlace.Completion.ringEquivRealOfIsReal hw)
      fun x => ?_
    rw [InfinitePlace.Completion.ringEquivRealOfIsReal_apply]
    exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero
      (map_zero _) x
  · refine exists_normedSpace_real_of_ringEquiv
      (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw) fun x => ?_
    rw [InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply]
    exact (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero
      (map_zero _) x

end RealStructure

section Determinant

variable (F : Type u) [Field F] [NumberField F]

/-- The Haar character of a linear automorphism with the determinant of `Ad(g)` is the local
norm of the adjoint determinant character at `g`. -/
theorem addEquivAddHaarChar_placeLinear_eq_localCharacterNorm
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (i : Place F) (g : PlaceGroupPoints F G i) {d : ℕ}
    [MeasurableSpace (Fin d → placeCompletion F i)] [BorelSpace (Fin d → placeCompletion F i)]
    (A : (Fin d → placeCompletion F i) ≃ₗ[placeCompletion F i] (Fin d → placeCompletion F i))
    (hA : LinearMap.det (A : (Fin d → placeCompletion F i) →ₗ[placeCompletion F i]
        (Fin d → placeCompletion F i)) =
      LinearMap.det (Langlands.GroupScheme.adjoint G (placeCompletion F i) g)) :
    addEquivAddHaarChar (placeLinearContinuousAddEquiv F i A) =
      (AdelicGroupPoints.localCharacterNorm F G
        (Langlands.GroupScheme.Lie.adjointDeterminantCharacter G).toMul i g : ℝ≥0) := by
  rw [addEquivAddHaarChar_placeLinear_eq_placeNorm]
  change (placeNorm F i (LinearEquiv.det A) : ℝ≥0) =
    (placeNorm F i (AdelicGroupPoints.characterUnits F G
      (Langlands.GroupScheme.Lie.adjointDeterminantCharacter G).toMul
      (placeCompletion F i) g) : ℝ≥0)
  have h : LinearEquiv.det A = AdelicGroupPoints.characterUnits F G
      (Langlands.GroupScheme.Lie.adjointDeterminantCharacter G).toMul (placeCompletion F i) g := by
    apply Units.ext
    rw [LinearEquiv.coe_det, hA]
    exact (Langlands.GroupScheme.Lie.adjointDeterminantCharacter_val G (placeCompletion F i) g).symm
  rw [h]

end Determinant

end Langlands.Global
