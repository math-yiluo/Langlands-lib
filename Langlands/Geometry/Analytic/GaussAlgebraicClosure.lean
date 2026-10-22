import Langlands.Geometry.Analytic.TateGaussPoint
import Langlands.Geometry.Analytic.Spectrum.ResidueField
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm

/-! # An actual normed algebraic closure above the Gauss point -/

noncomputable section

universe u

namespace Langlands.Analytic.StrictTateAlgebra

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
  (n : ℕ)

/-- The completed residue field of the actual Gauss seminorm. -/
abbrev GaussCompletion :=
  BanachSpectrum.CompletedResidueField K (gaussPoint (K := K) n)

instance gaussCompletionAlgebra :
    Algebra (StrictTateAlgebra (Fin n) K) (GaussCompletion K n) :=
  (BanachSpectrum.completedResidueMap K (gaussPoint (K := K) n)).toAlgHom.toRingHom.toAlgebra

@[simp]
theorem norm_gaussCompletion_algebraMap (a : StrictTateAlgebra (Fin n) K) :
    ‖algebraMap (StrictTateAlgebra (Fin n) K) (GaussCompletion K n) a‖ = ‖a‖ :=
  BanachSpectrum.norm_completedResidueMap K (gaussPoint (K := K) n) a

instance gaussCompletionFaithful :
    FaithfulSMul (StrictTateAlgebra (Fin n) K) (GaussCompletion K n) :=
  (faithfulSMul_iff_algebraMap_injective _ _).mpr <|
    (injective_iff_map_eq_zero _).mpr fun a ha => by
      have := norm_gaussCompletion_algebraMap K n a
      rw [ha, norm_zero] at this
      exact norm_eq_zero.mp this.symm

instance gaussCompletionScalarTower :
    IsScalarTower K (StrictTateAlgebra (Fin n) K) (GaussCompletion K n) :=
  IsScalarTower.of_algebraMap_eq fun a =>
    (BanachSpectrum.completedResidueMap K (gaussPoint (K := K) n)).toAlgHom.commutes a

instance gaussCompletionNontriviallyNormedField :
    NontriviallyNormedField (GaussCompletion K n) := by
  let h : NormedField (GaussCompletion K n) := inferInstance
  refine { toNormedField := h, non_trivial := ?_ }
  obtain ⟨a, ha⟩ := NormedField.exists_one_lt_norm K
  exact ⟨algebraMap K (GaussCompletion K n) a, by simpa using ha⟩

/-- The algebraic closure of the constructed complete Gauss residue field,
with its norm supplied by the norm-extension theorem. -/
abbrev GaussAlgebraicClosure := AlgebraicClosure (GaussCompletion K n)

instance gaussClosureNormedField : NormedField (GaussAlgebraicClosure K n) :=
  spectralNorm.normedField (GaussCompletion K n) (GaussAlgebraicClosure K n)

instance gaussClosureNormedAlgebra :
    NormedAlgebra (GaussCompletion K n) (GaussAlgebraicClosure K n) :=
  spectralNorm.normedAlgebra (GaussCompletion K n) (GaussAlgebraicClosure K n)

instance gaussClosureBaseNormedAlgebra : NormedAlgebra K (GaussAlgebraicClosure K n) where
  norm_smul_le a b := by
    rw [Algebra.smul_def, norm_mul,
      IsScalarTower.algebraMap_apply K (GaussCompletion K n) (GaussAlgebraicClosure K n),
      norm_algebraMap', norm_algebraMap']

@[simp]
theorem norm_gaussClosure_algebraMap (a : StrictTateAlgebra (Fin n) K) :
    ‖algebraMap (StrictTateAlgebra (Fin n) K) (GaussAlgebraicClosure K n) a‖ = ‖a‖ := by
  rw [IsScalarTower.algebraMap_apply (StrictTateAlgebra (Fin n) K)
    (GaussCompletion K n) (GaussAlgebraicClosure K n)]
  rw [norm_algebraMap', norm_gaussCompletion_algebraMap]

instance gaussClosureFaithful :
    FaithfulSMul (StrictTateAlgebra (Fin n) K) (GaussAlgebraicClosure K n) :=
  (faithfulSMul_iff_algebraMap_injective _ _).mpr <|
    (injective_iff_map_eq_zero _).mpr fun a ha => by
      have := norm_gaussClosure_algebraMap K n a
      rw [ha, norm_zero] at this
      exact norm_eq_zero.mp this.symm

instance gaussClosureFractionAlgebra :
    Algebra (FractionRing (StrictTateAlgebra (Fin n) K)) (GaussAlgebraicClosure K n) :=
  FractionRing.liftAlgebra _ _

instance gaussClosureFractionScalarTower :
    IsScalarTower (StrictTateAlgebra (Fin n) K)
      (FractionRing (StrictTateAlgebra (Fin n) K)) (GaussAlgebraicClosure K n) :=
  FractionRing.isScalarTower_liftAlgebra _ _

instance gaussClosureUltrametric : IsUltrametricDist (GaussAlgebraicClosure K n) :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm
    (isNonarchimedean_spectralNorm (K := GaussCompletion K n)
      (L := GaussAlgebraicClosure K n))

end Langlands.Analytic.StrictTateAlgebra
