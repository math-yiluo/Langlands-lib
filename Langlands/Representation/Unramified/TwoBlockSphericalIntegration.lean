import Langlands.Group.GL.LocalFieldTopology
import Langlands.Representation.GodementJacquet.TwoBlockParabolicHaar
import Langlands.Representation.Unramified.SphericalProductVector

/-! Spherical normalization of the integral in two-block parabolic coordinates. -/

noncomputable section

namespace Langlands.Unramified

open MeasureTheory MeasureTheory.Measure TopologicalSpace
open Langlands.Correspondence Langlands.GeneralLinear
open Langlands.RankinSelberg Langlands.RankinSelberg.TwoBlockJacquet
open Langlands.GodementJacquet.TwoBlock

universe u

section IntegralEntries

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
variable {R : Type u} [Field R] (O : Subring R)

private theorem matrix_mul_entries_mem {ι κ η : Type*} [Fintype κ]
    {A : Matrix ι κ R} {C : Matrix κ η R}
    (hA : ∀ i j, A i j ∈ O) (hC : ∀ i j, C i j ∈ O) :
    ∀ i j, (A * C) i j ∈ O := by
  intro i j
  rw [Matrix.mul_apply]
  exact O.sum_mem fun k _ => O.mul_mem (hA i k) (hC k j)

private theorem parabolicPoint_entries_mem_iff (L : (succBlockShape m h).Levi R)
    (x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) R) :
    (∀ i j, (parabolicPoint h (L, x)).val i j ∈ O) ↔
      (∀ i j, (L 0).val i j ∈ O) ∧ (∀ i j, (L 1).val i j ∈ O) ∧
        (∀ i j, ((L 0).val * x) i j ∈ O) := by
  rw [parabolicPoint_val]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
  constructor
  · intro hz
    have hEntries (i j : Fin (m 0 + 1) ⊕ Fin (m 1 + 1)) :
        Matrix.fromBlocks (L 0).val ((L 0).val * x) 0 (L 1).val i j ∈ O := by
      simpa only [Equiv.symm_apply_apply] using hz (blockEquiv h i) (blockEquiv h j)
    exact ⟨fun i j => hEntries (.inl i) (.inl j), fun i j => hEntries (.inr i) (.inr j),
      fun i j => hEntries (.inl i) (.inr j)⟩
  · rintro ⟨hA, hD, hX⟩ i j
    rcases (blockEquiv h).symm i with a | a <;> rcases (blockEquiv h).symm j with b | b
    · exact hA a b
    · exact hX a b
    · exact O.zero_mem
    · exact hD a b

/-- Put a block diagonal right factor after the radical coordinate. -/
theorem parabolicPoint_mul_levi_right (L k : (succBlockShape m h).Levi R)
    (x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) R) :
    parabolicPoint h (L * k, x) =
      parabolicPoint h (L, (k 0).val * x * ((k 1)⁻¹ : GeneralLinear (m 1 + 1) R).val) *
        (succBlockShape m h).leviEmbedding R k := by
  let y := (k 0).val * x * ((k 1)⁻¹ : GeneralLinear (m 1 + 1) R).val
  have hCancel : ((k 0)⁻¹ : GeneralLinear (m 0 + 1) R).val * y * (k 1).val = x := by
    dsimp only [y]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, Matrix.one_mul, Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, Matrix.mul_one]
  change parabolicPoint h (L * k, x) =
    parabolicPoint h (L, y) * (succBlockShape m h).leviEmbedding R k
  rw [parabolicPoint, parabolicPoint, mul_assoc, upperRadical_mul_leviEmbedding, hCancel,
    ← mul_assoc, ← map_mul]

/-- Integral invertibility in the ambient group is equivalent to integral
invertibility in both diagonal blocks and integrality of the radical coordinate. -/
theorem parabolicPoint_mem_integralSubgroup_iff (L : (succBlockShape m h).Levi R)
    (x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) R) :
    parabolicPoint h (L, x) ∈ Conductor.integralSubgroup O t ↔
      (∀ i : Fin 2, L i ∈ Conductor.integralSubgroup O (m i)) ∧
        (∀ a b, x a b ∈ O) := by
  let y := -((L 0).val * x * ((L 1)⁻¹ : GeneralLinear (m 1 + 1) R).val)
  have hone : parabolicPoint (R := R) h (1, 0) = 1 := by
    simp [parabolicPoint]
  have hinv : (parabolicPoint h (L, x))⁻¹ = parabolicPoint h (L⁻¹, y) := by
    have hi := parabolicPoint_inv_mul h L 1 x 0
    rw [hone] at hi
    simpa only [mul_one, zero_sub, Pi.inv_apply, inv_inv, y] using hi
  rw [Conductor.mem_integralSubgroup, hinv, parabolicPoint_entries_mem_iff,
    parabolicPoint_entries_mem_iff]
  simp only [Pi.inv_apply]
  constructor
  · rintro ⟨⟨hA, hD, hX⟩, hAi, hDi, _⟩
    refine ⟨?_, ?_⟩
    · intro i
      fin_cases i
      · exact (Conductor.mem_integralSubgroup O _ _).mpr ⟨hA, hAi⟩
      · exact (Conductor.mem_integralSubgroup O _ _).mpr ⟨hD, hDi⟩
    · have hcancel : ((L 0)⁻¹ : GeneralLinear (m 0 + 1) R).val * ((L 0).val * x) = x := by
        rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
      exact hcancel ▸ matrix_mul_entries_mem O hAi hX
  · rintro ⟨hL, hx⟩
    obtain ⟨hA, hAi⟩ := (Conductor.mem_integralSubgroup O _ _).mp (hL 0)
    obtain ⟨hD, hDi⟩ := (Conductor.mem_integralSubgroup O _ _).mp (hL 1)
    have hX := matrix_mul_entries_mem O hA hx
    have hy : ∀ a b, y a b ∈ O :=
      fun a b => O.neg_mem (matrix_mul_entries_mem O hX hDi a b)
    exact ⟨⟨hA, hD, hX⟩, hAi, hDi, matrix_mul_entries_mem O hAi hy⟩

end IntegralEntries

section Haar

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)

attribute [local instance] heckeFieldTopology heckeFieldValuativeRel heckeFieldLocalField
  heckeGeneralLinearTopology heckeGeneralLinearTopologicalGroup heckeGeneralLinearT2
  heckeGeneralLinearMeasurable heckeGeneralLinearBorel

local instance twoBlockIntegrationFieldMeasurable : MeasurableSpace F.Carrier := borel _
local instance twoBlockIntegrationFieldBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance twoBlockIntegrationFieldSecondCountable : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance twoBlockIntegrationGLSigmaCompact (n : ℕ) :
    SigmaCompactSpace (GeneralLinear n F.Carrier) :=
  LocalFieldTopology.generalLinear_sigmaCompactSpace F.Carrier n
local instance twoBlockIntegrationMatrixSigmaCompact (a b : ℕ) :
    SigmaCompactSpace (Matrix (Fin a) (Fin b) F.Carrier) :=
  inferInstanceAs (SigmaCompactSpace (Fin a → Fin b → F.Carrier))

local notation "𝒪" => Valuation.integer (ValuativeRel.valuation F.Carrier)

theorem sphericalHaar_eq_generalLinearHaar (r : ℕ) :
    sphericalHaar F r = generalLinearHaar F.Carrier r := by
  unfold sphericalHaar generalLinearHaar normalizedCompactOpenHaar
  congr 1
  apply PositiveCompacts.ext
  change (sphericalSubgroup F r : Set (GeneralLinear (r + 1) F.Carrier)) =
    (Conductor.levelSubgroup F.Carrier r 0 : Set (GeneralLinear (r + 1) F.Carrier))
  rw [Conductor.levelSubgroup_zero]
  rfl

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

/-- The integral block factors embed into the ambient spherical subgroup. -/
theorem leviEmbedding_mem_spherical_of_forall (k : (succBlockShape m h).Levi F.Carrier)
    (hk : ∀ i : Fin 2, k i ∈ sphericalOpenSubgroup F (m i)) :
    (succBlockShape m h).leviEmbedding F.Carrier k ∈ sphericalOpenSubgroup F t := by
  have hm := (parabolicPoint_mem_integralSubgroup_iff h 𝒪 k 0).mpr ⟨hk, by simp⟩
  change (succBlockShape m h).leviEmbedding F.Carrier k ∈ Conductor.integralSubgroup 𝒪 t
  simpa only [parabolicPoint, upperRadical_zero, mul_one] using hm

theorem determinantNorm_eq_one_of_mem_spherical {r : ℕ} {g : GeneralLinear (r + 1) F.Carrier}
    (hg : g ∈ sphericalOpenSubgroup F r) :
    F.canonicalTopologicalData.determinantNorm (r + 1) g = 1 := by
  obtain ⟨hEntries, hInverse⟩ := (Conductor.mem_integralSubgroup 𝒪 r g).mp hg
  exact SphericalExistence.determinantNorm_eq_one_of_integral F F.canonicalTopologicalData
    g hEntries hInverse

theorem leviHalfModulus_eq_one_of_forall_spherical
    (k : (succBlockShape m h).Levi F.Carrier)
    (hk : ∀ i : Fin 2, k i ∈ sphericalOpenSubgroup F (m i)) :
    F.canonicalTopologicalData.leviHalfModulus (succBlockShape m h) k = 1 := by
  let T := F.canonicalTopologicalData
  have hNorm : k ∈ T.normOneLevi (succBlockShape m h) :=
    (T.mem_normOneLevi _ _).mpr fun i => determinantNorm_eq_one_of_mem_spherical F (hk i)
  exact (T.leviHalfModulus_eq_one _ _).mpr (T.normOneLevi_le_ker_leviModulus _ hNorm)

variable (dx : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier))
  [dx.IsAddHaarMeasure]

/-- The spherical parabolic coordinates have mass one on the preimage of the
standard compact when the radical Haar gives the integral rectangles mass one. -/
theorem parabolicMeasure_preimage_spherical
    (hdx : dx {x | ∀ a b, x a b ∈ 𝒪} = 1) :
    parabolicMeasure F h dx (parabolicPoint h ⁻¹' (sphericalOpenSubgroup F t : Set _)) = 1 := by
  have hpre : parabolicPoint h ⁻¹' (sphericalOpenSubgroup F t : Set _) =
      (Set.univ.pi fun i : Fin 2 =>
        (sphericalOpenSubgroup F (m i) : Set (GeneralLinear (m i + 1) F.Carrier))) ×ˢ
        {x | ∀ a b, x a b ∈ 𝒪} := by
    ext ⟨L, x⟩
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_pi, Set.mem_univ, forall_const,
      Set.mem_ofPred_eq]
    exact parabolicPoint_mem_integralSubgroup_iff h 𝒪 L x
  rw [hpre, parabolicMeasure, Measure.prod_prod, Measure.pi_pi, hdx, mul_one]
  simp only [← sphericalHaar_eq_generalLinearHaar, sphericalHaar_self, Finset.prod_const_one]

/-- Integrability and the volume-one formula for right spherical-invariant functions
in the existing two-block parabolic coordinates. -/
theorem integrable_integral_parabolicPoint_of_right_sphericalInvariant {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    {f : GeneralLinear (t + 1) F.Carrier → V}
    (hdx : dx {x | ∀ a b, x a b ∈ 𝒪} = 1) (hf : Integrable f (sphericalHaar F t))
    (hinv : ∀ g (k : sphericalOpenSubgroup F t), f (g * k.val) = f g) :
    Integrable (fun z => f (parabolicPoint h z)) (parabolicMeasure F h dx) ∧
      ∫ z, f (parabolicPoint h z) ∂(parabolicMeasure F h dx) =
        ∫ g, f g ∂(sphericalHaar F t) := by
  let K := sphericalOpenSubgroup F t
  have hPK (g : GeneralLinear (t + 1) F.Carrier) :
      ∃ (q : (succBlockShape m h).parabolic F.Carrier) (k : K), g = q.val * k.val := by
    obtain ⟨q, k, hk, he⟩ := SphericalProduct.exists_parabolic_mul_spherical
      F (succBlockShape m h) g
    exact ⟨q, ⟨k, hk⟩, he⟩
  have hf' : Integrable f (generalLinearHaar F.Carrier t) :=
    (sphericalHaar_eq_generalLinearHaar F t) ▸ hf
  have hPair := (integrable_parabolic_iff F h dx K
    (sphericalOpenSubgroup_isCompact F t) hPK hf'.aestronglyMeasurable).mpr hf'
  rw [← sphericalHaar_eq_generalLinearHaar] at hPair
  let ν := (sphericalHaar F t).restrict (K : Set (GeneralLinear (t + 1) F.Carrier))
  let : IsProbabilityMeasure ν := ⟨by simp [ν, K]⟩
  change Integrable _ (ν.prod (parabolicMeasure F h dx)) at hPair
  have hK : ∀ᵐ k ∂ν, k ∈ (K : Set (GeneralLinear (t + 1) F.Carrier)) :=
    ae_restrict_mem K.isOpen.measurableSet
  obtain ⟨k, hk, hkInt⟩ := (hK.and hPair.prod_right_ae).exists
  refine ⟨hkInt.congr (ae_of_all _ fun z => hinv (parabolicPoint h z) ⟨k, hk⟩), ?_⟩
  have hInt := integral_parabolic F h dx K (sphericalOpenSubgroup_isCompact F t) hPK hf'
  rw [← sphericalHaar_eq_generalLinearHaar, parabolicMeasure_preimage_spherical F h dx hdx,
    ENNReal.toReal_one, one_smul] at hInt
  have hConst : Set.EqOn (fun k : GeneralLinear (t + 1) F.Carrier =>
      ∫ z, f (parabolicPoint h z * k) ∂(parabolicMeasure F h dx))
      (fun _ => ∫ z, f (parabolicPoint h z) ∂(parabolicMeasure F h dx)) K := by
    intro k hk
    exact integral_congr_ae (ae_of_all _ fun z => hinv (parabolicPoint h z) ⟨k, hk⟩)
  rwa [setIntegral_congr_fun K.isOpen.measurableSet hConst, setIntegral_const,
    sphericalHaar_real_self, one_smul] at hInt

end Haar

end Langlands.Unramified
