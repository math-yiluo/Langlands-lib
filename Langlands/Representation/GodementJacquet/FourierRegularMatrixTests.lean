import Langlands.HarmonicAnalysis.RectangularFourierEquiv
import Langlands.Representation.RankinSelberg.LastRowCompactOrbitProof

/-!
# Matrix tests with regular support on both Fourier sides

This auxiliary space records only the two support properties used in the
supercuspidal functional-equation argument.
-/

noncomputable section

namespace Langlands.GodementJacquet

open HarmonicAnalysis

universe uK

variable {K : Type uK} [Field K] [TopologicalSpace K] (d : ℕ)

/-- Full-matrix tests vanishing at every noninvertible matrix. -/
def regularMatrixTests :
    Submodule ℂ (SchwartzBruhat (Matrix (Fin d) (Fin d) K)) where
  carrier := {Φ | ∀ A, ¬ IsUnit A → Φ A = 0}
  zero_mem' := by intro A _; rfl
  add_mem' {Φ Ψ} hΦ hΨ := by
    intro A hA
    change Φ A + Ψ A = 0
    rw [hΦ A hA, hΨ A hA, add_zero]
  smul_mem' c Φ hΦ := by
    intro A hA
    change c • Φ A = 0
    rw [hΦ A hA, smul_zero]

theorem mem_regularMatrixTests_iff
    (Φ : SchwartzBruhat (Matrix (Fin d) (Fin d) K)) :
    Φ ∈ regularMatrixTests (K := K) d ↔
      ∀ A, ¬ IsUnit A → Φ A = 0 := Iff.rfl

/-- The actual topological support of a regular test consists of invertible
matrices, since a locally constant test has closed nonvanishing support. -/
theorem tsupport_subset_units_of_mem_regularMatrixTests
    {Φ : SchwartzBruhat (Matrix (Fin d) (Fin d) K)}
    (hΦ : Φ ∈ regularMatrixTests (K := K) d) :
    tsupport (Φ : Matrix (Fin d) (Fin d) K → ℂ) ⊆
      Set.range (Units.val : GeneralLinear d K → Matrix (Fin d) (Fin d) K) := by
  rw [Hecke.TestFunction.tsupport_eq_support]
  intro A hA
  by_contra h
  apply hA
  apply hΦ A
  rintro ⟨u, rfl⟩
  exact h ⟨u, rfl⟩

variable [IsTopologicalDivisionRing K]

/-- Restricting a full-matrix regular test to the actual general linear group
retains compact support in that group's topology. -/
theorem hasCompactSupport_restrict_of_mem_regularMatrixTests
    {Φ : SchwartzBruhat (Matrix (Fin d) (Fin d) K)}
    (hΦ : Φ ∈ regularMatrixTests (K := K) d) :
    HasCompactSupport (fun g : GeneralLinear d K => Φ g.val) := by
  have hc : IsCompact ((Units.val : GeneralLinear d K →
      Matrix (Fin d) (Fin d) K) ⁻¹' tsupport (Φ : Matrix (Fin d) (Fin d) K → ℂ)) :=
    (RankinSelberg.isEmbedding_generalLinear_val d).isInducing.isCompact_preimage'
      Φ.hasCompactSupport (tsupport_subset_units_of_mem_regularMatrixTests d hΦ)
  exact HasCompactSupport.intro hc fun g hg =>
    image_eq_zero_of_notMem_tsupport hg

/-- The regular matrix test regarded as a group Schwartz–Bruhat function. -/
def regularMatrixTestRestriction :
    regularMatrixTests (K := K) d →ₗ[ℂ] SchwartzBruhat (GeneralLinear d K) where
  toFun Φ := ⟨fun g => Φ.val g.val,
    Φ.val.locallyConstant.comp_continuous Units.continuous_val,
    hasCompactSupport_restrict_of_mem_regularMatrixTests d Φ.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem regularMatrixTestRestriction_apply
    (Φ : regularMatrixTests (K := K) d) (g : GeneralLinear d K) :
    regularMatrixTestRestriction d Φ g = Φ.val g.val := rfl

variable [MeasurableSpace K] [BorelSpace K] [LocallyCompactSpace K]
  [TotallyDisconnectedSpace K] [T2Space K]
  (ψ : UnitaryAdditiveCharacter K) (ν : AdditiveHaarMeasure K)
  (hsd : IsSelfDual ψ ν)

/-- Tests whose original and actual plus Fourier transforms both vanish on
singular matrices. This is an internal support-based auxiliary space. -/
def fourierRegularMatrixTests :
    Submodule ℂ (SchwartzBruhat (Matrix (Fin d) (Fin d) K)) :=
  regularMatrixTests d ⊓
    (regularMatrixTests d).comap (rectangularFourierEquiv ψ ν d d hsd).toLinearMap

theorem mem_fourierRegularMatrixTests_iff
    (Φ : SchwartzBruhat (Matrix (Fin d) (Fin d) K)) :
    Φ ∈ fourierRegularMatrixTests d ψ ν hsd ↔
      (∀ A, ¬ IsUnit A → Φ A = 0) ∧
      ∀ A, ¬ IsUnit A → rectangularFourierEquiv ψ ν d d hsd Φ A = 0 := Iff.rfl

/-- The auxiliary space is stable under the full plus Fourier transform with
the supplied scalar self-dual measure. -/
theorem fourier_mem_fourierRegularMatrixTests
    {Φ : SchwartzBruhat (Matrix (Fin d) (Fin d) K)}
    (hΦ : Φ ∈ fourierRegularMatrixTests d ψ ν hsd) :
    rectangularFourierEquiv ψ ν d d hsd Φ ∈
      fourierRegularMatrixTests d ψ ν hsd := by
  refine ⟨hΦ.2, ?_⟩
  intro A hA
  change rectangularFourierEquiv ψ ν d d hsd
    (rectangularFourierEquiv ψ ν d d hsd Φ) A = 0
  rw [rectangularFourierEquiv_apply_apply]
  apply hΦ.1 (-A)
  intro hneg
  exact hA (by simpa using hneg.neg)

/-- The inverse Fourier transform preserves the same auxiliary space. -/
theorem inverseFourier_mem_fourierRegularMatrixTests
    {Φ : SchwartzBruhat (Matrix (Fin d) (Fin d) K)}
    (hΦ : Φ ∈ fourierRegularMatrixTests d ψ ν hsd) :
    (rectangularFourierEquiv ψ ν d d hsd).symm Φ ∈
      fourierRegularMatrixTests d ψ ν hsd := by
  refine ⟨?_, ?_⟩
  · intro A hA
    rw [rectangularFourierEquiv_symm_apply, ← rectangularFourierEquiv_apply ψ ν d d hsd]
    apply hΦ.2 (-A)
    intro hneg
    exact hA (by simpa using hneg.neg)
  · change rectangularFourierEquiv ψ ν d d hsd
      ((rectangularFourierEquiv ψ ν d d hsd).symm Φ) ∈ regularMatrixTests d
    simpa using hΦ.1

/-- Both sides of a Fourier-regular test have actual compact support on GL. -/
theorem fourierRegularMatrixTests_compact_support
    {Φ : SchwartzBruhat (Matrix (Fin d) (Fin d) K)}
    (hΦ : Φ ∈ fourierRegularMatrixTests d ψ ν hsd) :
    HasCompactSupport (fun g : GeneralLinear d K => Φ g.val) ∧
      HasCompactSupport (fun g : GeneralLinear d K =>
        rectangularFourierEquiv ψ ν d d hsd Φ g.val) :=
  ⟨hasCompactSupport_restrict_of_mem_regularMatrixTests d hΦ.1,
    hasCompactSupport_restrict_of_mem_regularMatrixTests d hΦ.2⟩

end Langlands.GodementJacquet
