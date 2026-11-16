import Langlands.Geometry.Analytic.ValuedField.AlgebraicEmbedding

/-! # Lifting a prescribed character along an algebraic residue extension -/

noncomputable section

universe uK uA uB uL

namespace Langlands.Analytic.BanachSpectrum

variable (K : Type uK) [NormedField K] [IsUltrametricDist K]
  {A : Type uA} {B : Type uB} [NormedCommRing A] [NormedCommRing B]
  [NormedAlgebra K A] [NormedAlgebra K B]

/-- Algebraicity of the canonical map between the actual completed residue
fields of a bounded map and a spectrum point. -/
def IsAlgebraicCompletedResidueComap (f : BoundedAlgHom K A B) (y : BanachSpectrum B) :
    Prop :=
  letI := (completedResidueComap K f y).toAlgHom.toRingHom.toAlgebra
  Algebra.IsAlgebraic
    (CompletedResidueField K (comap f.toBoundedRingHom y)) (CompletedResidueField K y)

variable {L : Type uL} [NormedField L] [IsUltrametricDist L] [CompleteSpace L]
  [IsAlgClosed L] [Algebra K L]

/-- If the completed residue extension at `y` is algebraic, every prescribed
character realizing its image extends to a character realizing `y`. -/
theorem exists_character_lift_of_isAlgebraic_completedResidueComap
    (f : BoundedAlgHom K A B) (y : BanachSpectrum B)
    (halg : IsAlgebraicCompletedResidueComap K f y)
    (g : A →ₐ[K] L) (hg : ∀ a, ‖g a‖ = (comap f.toBoundedRingHom y) a) :
    ∃ h : BoundedAlgHom K B L,
      (∀ b, ‖h b‖ = y b) ∧ ∀ a, h (f a) = g a := by
  let E := CompletedResidueField K (comap f.toBoundedRingHom y)
  let F := CompletedResidueField K y
  let ρ := completedResidueComap K f y
  let : NormedAlgebra E F :=
    { toAlgebra := ρ.toAlgHom.toRingHom.toAlgebra
      norm_smul_le := fun c z => by
        change ‖ρ c * z‖ ≤ ‖c‖ * ‖z‖
        rw [norm_mul, (isometry_completedResidueComap K f y).norm_map_of_map_zero
          (map_zero _) c] }
  let : IsScalarTower K E F :=
    IsScalarTower.of_algebraMap_eq fun c => (ρ.toAlgHom.commutes c).symm
  let : Algebra.IsAlgebraic E F := halg
  let i := completedResidueLift K (comap f.toBoundedRingHom y) g hg
  obtain ⟨j, hj, hji⟩ := exists_isometric_algebraic_extension (F := F) i.toAlgHom
    (isometry_completedResidueLift K _ g hg)
  refine ⟨j.comp (completedResidueMap K y), ?_, ?_⟩
  · intro b
    change ‖j (completedResidueMap K y b)‖ = y b
    rw [hj.norm_map_of_map_zero (map_zero _), norm_completedResidueMap]
  · intro a
    change j (completedResidueMap K y (f a)) = g a
    rw [← completedResidueComap_map K f y a]
    exact (hji (completedResidueMap K (comap f.toBoundedRingHom y) a)).trans
      (completedResidueLift_map K _ g hg a)

end Langlands.Analytic.BanachSpectrum
