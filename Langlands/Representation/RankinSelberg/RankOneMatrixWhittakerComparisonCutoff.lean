import Langlands.Representation.RankinSelberg.RankOneMatrixWhittakerComparisonValues
import Langlands.Representation.RankinSelberg.UnequalRankSmearingAverage
import Langlands.HarmonicAnalysis.ScalarFourierClosureProof
import Langlands.HarmonicAnalysis.PadicSelfDualMeasureExistsProof
import Langlands.Group.GL.MirabolicTailConullProof

/-!
# Fourier cutoff along the rank-one embedding

For `σ` smooth on `GL_(m+2)`, a standard functional `ℓ`, a model function `W` of `ℓ`
and a Schwartz–Bruhat function `φ` on `F`, there is a model function `W'` of the
same `ℓ` with `W'(diag(det g, 1, …, 1)) = φ(det g) W(diag(det g, 1, …, 1))` for every
`g ∈ GL₁`. The function `W'` is the right smearing of `W` along `x ↦ 1 + x E₀₁`
against a Fourier preimage of `φ`.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear

universe uF uV

section Matrix

variable {F : Type uF} [Field F]

theorem rankOneCutoff_index_ne (m : ℕ) : (0 : Fin (m + 1 + 1)) ≠ 1 := by
  intro h
  have hv := congrArg Fin.val h
  simp at hv

/-- The transvection `1 + x E₀₁` of `GL_(m+2)`. -/
def rankOneCutoffUnipotent (m : ℕ) (x : F) : Langlands.GeneralLinear (m + 1 + 1) F :=
  transvectionUnit 0 1 (rankOneCutoff_index_ne m) x

theorem rankOneCutoffUnipotent_apply (m : ℕ) (x : F) (i j : Fin (m + 1 + 1)) :
    rankOneCutoffUnipotent m x i j =
      (if i = j then 1 else 0) + if i = 0 ∧ j = 1 then x else 0 := by
  simp [rankOneCutoffUnipotent, transvectionUnit, Matrix.transvection, Matrix.one_apply,
    Matrix.single_apply, eq_comm]

/-- `1 + x E₀₁` is upper unipotent. -/
theorem rankOneCutoffUnipotent_mem (m : ℕ) (x : F) :
    rankOneCutoffUnipotent m x ∈ upperUnipotent (m + 1 + 1) F := by
  refine ⟨?_, ?_⟩
  · intro i j hij
    change rankOneCutoffUnipotent m x i j = 0
    rw [rankOneCutoffUnipotent_apply]
    have hne : i ≠ j := fun h => (lt_irrefl j) (h ▸ hij)
    rw [ite_eq_right hne, ite_eq_right]
    · simp
    · rintro ⟨rfl, rfl⟩
      have hv : (1 : Fin (m + 1 + 1)).val < (0 : Fin (m + 1 + 1)).val := hij
      simp at hv
  · intro i
    change rankOneCutoffUnipotent m x i i = 1
    rw [rankOneCutoffUnipotent_apply, ite_eq_left rfl, ite_eq_right]
    · simp
    · rintro ⟨rfl, h⟩
      exact rankOneCutoff_index_ne m h

/-- `diag(det g, 1, …, 1) (1 + x E₀₁) = (1 + (det g) x E₀₁) diag(det g, 1, …, 1)`. -/
theorem rankOneEmbedding_mul_cutoffUnipotent (m : ℕ) (g : Langlands.GeneralLinear (0 + 1) F)
    (x : F) :
    rankOneEmbedding m g * rankOneCutoffUnipotent m x =
      rankOneCutoffUnipotent m (((Matrix.GeneralLinearGroup.det g : Fˣ) : F) * x) *
        rankOneEmbedding m g := by
  apply Units.ext
  ext i j
  change (Matrix.diagonal _ * Matrix.transvection 0 1 x :
      Matrix (Fin (m + 1 + 1)) (Fin (m + 1 + 1)) F) i j =
    (Matrix.transvection 0 1 _ * Matrix.diagonal _ :
      Matrix (Fin (m + 1 + 1)) (Fin (m + 1 + 1)) F) i j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  have h1 := rankOneCutoffUnipotent_apply m x i j
  have h2 := rankOneCutoffUnipotent_apply m
    (((Matrix.GeneralLinearGroup.det g : Fˣ) : F) * x) i j
  change Matrix.transvection 0 1 x i j = _ at h1
  change Matrix.transvection 0 1 _ i j = _ at h2
  rw [h1, h2]
  by_cases hij : i = j
  · subst hij
    have hii : ¬(i = 0 ∧ i = 1) := fun h => rankOneCutoff_index_ne m (h.1.symm.trans h.2)
    rw [ite_eq_left rfl, ite_eq_right hii, ite_eq_right hii]
    ring
  · rw [ite_eq_right hij]
    by_cases h01 : i = 0 ∧ j = 1
    · obtain ⟨rfl, rfl⟩ := h01
      have h01' : (0 : Fin (m + 1 + 1)) = 0 ∧ (1 : Fin (m + 1 + 1)) = 1 := ⟨rfl, rfl⟩
      rw [ite_eq_left h01', ite_eq_left h01', Fin.cons_zero, Fin.cons_one]
      simp
    · rw [ite_eq_right h01, ite_eq_right h01]
      simp

end Matrix

section Character

variable {F : Type uF} [Field F] [TopologicalSpace F]

/-- The standard character takes the value `ψ(x)` on `1 + x E₀₁`. -/
theorem standardCharacter_rankOneCutoffUnipotent (ψ : UnitaryAdditiveCharacter F) (m : ℕ)
    (x : F) :
    (standardCharacter ψ (m + 1)
        ⟨rankOneCutoffUnipotent m x, rankOneCutoffUnipotent_mem m x⟩ : ℂ) =
      ψ.complex x := by
  rw [standardCharacter_apply]
  congr 1
  rw [Finset.sum_eq_single 0]
  · change rankOneCutoffUnipotent m x _ _ = x
    rw [rankOneCutoffUnipotent_apply, ite_eq_right, ite_eq_left]
    · simp
    · exact ⟨rfl, rfl⟩
    · exact rankOneCutoff_index_ne m
  · intro b _ hb
    change rankOneCutoffUnipotent m x _ _ = 0
    rw [rankOneCutoffUnipotent_apply, ite_eq_right, ite_eq_right]
    · simp
    · rintro ⟨h, -⟩
      apply hb
      ext
      have hv := congrArg Fin.val h
      simpa using hv
    · intro h
      have hv := congrArg Fin.val h
      simp at hv
  · simp

end Character

section Cutoff

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [MeasurableSpace F] [BorelSpace F] [LocallyCompactSpace F] [T2Space F]
  [TotallyDisconnectedSpace F]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The Fourier cutoff along `rankOneEmbedding m` for a self-dual Haar measure. -/
theorem exists_rankOneCutoff_of_isSelfDual (ψ : UnitaryAdditiveCharacter F)
    (μ : AdditiveHaarMeasure F) (hμ : IsSelfDual ψ μ) {m : ℕ}
    (σ : Representation ℂ (Langlands.GeneralLinear (m + 1 + 1) F) V) (hσ : IsSmooth σ)
    (ℓ : glFunctionals ψ (m + 1) σ) (w : (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule)
    (φ : SchwartzBruhat F) :
    ∃ w' : (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule,
      ∀ g : Langlands.GeneralLinear (0 + 1) F,
        glModelFunction ψ (m + 1) σ ℓ w' (rankOneEmbedding m g) =
          φ ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) *
            glModelFunction ψ (m + 1) σ ℓ w (rankOneEmbedding m g) := by
  obtain ⟨-, hclosed⟩ := scalarFourierClosure F ψ μ hμ
  let φneg := Hecke.TestFunction.pullback (Homeomorph.neg F) φ
  obtain ⟨κ, hκ⟩ := hclosed φneg
  have hφκ : ∀ b, φ b = fourierIntegral ψ μ κ b := by
    intro b
    have hfun : (κ : F → ℂ) = fourierTransform ψ μ φneg := funext hκ
    calc φ b = φneg (-b) := by simp [φneg]
      _ = fourierIntegral ψ μ (fourierTransform ψ μ φneg) b := ((hμ φneg).2 b).symm
      _ = fourierIntegral ψ μ κ b := by rw [hfun]
  obtain ⟨w', hw'⟩ := Smearing.exists_coefficient_average μ.measure σ hσ ℓ
    (rankOneCutoffUnipotent m) (continuous_transvectionUnit _ _ (rankOneCutoff_index_ne m)) κ w
  refine ⟨w', fun g => ?_⟩
  have hcov : ∀ x : F,
      κ x * w.val.val (rankOneEmbedding m g * rankOneCutoffUnipotent m x) =
        (ψ.complex (x * ((Matrix.GeneralLinearGroup.det g : Fˣ) : F)) * κ x) *
          w.val.val (rankOneEmbedding m g) := by
    intro x
    have hθ := w.val.property
      ⟨rankOneCutoffUnipotent m (((Matrix.GeneralLinearGroup.det g : Fˣ) : F) * x),
        rankOneCutoffUnipotent_mem m _⟩ (rankOneEmbedding m g)
    rw [rankOneEmbedding_mul_cutoffUnipotent]
    erw [hθ]
    rw [standardCharacter_rankOneCutoffUnipotent, mul_comm _ x]
    ring
  change w'.val.val _ = _ * w.val.val _
  rw [(hw' _).2, funext hcov, integral_mul_const, hφκ]
  rfl

end Cutoff

/-- The Fourier cutoff along `rankOneEmbedding m` for the canonical topology of a
p-adic field: every `φ(det g)` multiple of a model function on the embedded `GL₁` is
the restriction of a model function of the same functional. -/
theorem exists_rankOneCutoff {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    {m : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (m + 1 + 1) F.Carrier) V) :
    letI := F.canonicalTopologicalData.topology
    IsSmooth σ →
    ∀ (ℓ : glFunctionals ψ (m + 1) σ) (w : (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule)
      (φ : SchwartzBruhat F.Carrier),
      ∃ w' : (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule,
        ∀ g : Langlands.GeneralLinear (0 + 1) F.Carrier,
          glModelFunction ψ (m + 1) σ ℓ w' (rankOneEmbedding m g) =
            φ ((Matrix.GeneralLinearGroup.det g : F.Carrierˣ) : F.Carrier) *
              glModelFunction ψ (m + 1) σ ℓ w (rankOneEmbedding m g) := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let := IsTopologicalAddGroup.rightUniformSpace F.Carrier
  let := isUniformAddGroup_of_addCommGroup (G := F.Carrier)
  let := borel F.Carrier
  have : BorelSpace F.Carrier := ⟨rfl⟩
  have : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
  intro hσ ℓ w φ
  obtain ⟨htd, hexists⟩ := padicSelfDualMeasureExists F F.canonicalTopologicalData
  obtain ⟨μ, hμ⟩ := hexists ψ
  exact exists_rankOneCutoff_of_isSelfDual ψ μ hμ σ hσ ℓ w φ

end Langlands.RankinSelberg
