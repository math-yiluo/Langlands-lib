import Langlands.Representation.RankinSelberg.TwoBlockDeformationCell
import Langlands.Analysis.Local.CompactFactorizationBochner
import Langlands.Representation.RankinSelberg.Measures
import Langlands.HarmonicAnalysis.PadicRectangularHaarScalingProof

/-!
# Haar measure of `GL_(t+1)` in two-block parabolic coordinates

For the upper parabolic `P` of the block shape `(m 0 + 1, m 1 + 1)`, every element
of `P` is `parabolicPoint (L, x) = leviEmbedding L * upperRadical x`, whose matrix is
`[[a, a x], [0, d]]` for `L = (a, d)`. With the parameter measure
`parabolicMeasure = (∏ normalized block Haar measures) × dx` (no density), left
translation in `P` is measure preserving, and for every compact open `K` with
`GL_(t+1) = P K` the Haar measure of `GL_(t+1)` factors through `K × P`
(Godement–Jacquet 1972, printed page 38, in its two-block form).
-/

noncomputable section

open MeasureTheory

namespace Langlands.GodementJacquet.TwoBlock

open GeneralLinear RankinSelberg RankinSelberg.TwoBlockJacquet RankinSelberg.TwoBlockDeformation

universe uF uR

section Algebra

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1) (R : Type uR) [CommRing R]

/-- The block coordinates `Fin (m 0 + 1) ⊕ Fin (m 1 + 1) ≃ Fin (t + 1)`. -/
def blockEquiv : Fin (m 0 + 1) ⊕ Fin (m 1 + 1) ≃ Fin (t + 1) :=
  finSumFinEquiv.trans (finCongr (blockRanks_add h))

theorem blockEquiv_inl (a : Fin (m 0 + 1)) :
    blockEquiv h (Sum.inl a) = (succBlockShape m h).index 0 a := by
  rw [index_zero]
  rfl

theorem blockEquiv_inr (b : Fin (m 1 + 1)) :
    blockEquiv h (Sum.inr b) = (succBlockShape m h).index 1 b := by
  rw [index_one]
  rfl

variable {R}

/-- A matrix of `GL_(t+1)` whose four blocks are known is the reindexed block matrix. -/
theorem val_eq_reindex_fromBlocks {g : GeneralLinear (t + 1) R}
    {A : Matrix (Fin (m 0 + 1)) (Fin (m 0 + 1)) R} {B : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) R}
    {C : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) R} {D : Matrix (Fin (m 1 + 1)) (Fin (m 1 + 1)) R}
    (h00 : ∀ a b, g ((succBlockShape m h).index 0 a) ((succBlockShape m h).index 0 b) = A a b)
    (h01 : ∀ a b, g ((succBlockShape m h).index 0 a) ((succBlockShape m h).index 1 b) = B a b)
    (h10 : ∀ a b, g ((succBlockShape m h).index 1 a) ((succBlockShape m h).index 0 b) = C a b)
    (h11 : ∀ a b, g ((succBlockShape m h).index 1 a) ((succBlockShape m h).index 1 b) = D a b) :
    g.val = Matrix.reindex (blockEquiv h) (blockEquiv h) (Matrix.fromBlocks A B C D) := by
  ext k l
  obtain ⟨s, rfl⟩ := (blockEquiv h).surjective k
  obtain ⟨s', rfl⟩ := (blockEquiv h).surjective l
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply]
  rcases s with a | a <;> rcases s' with b | b
  · rw [blockEquiv_inl, blockEquiv_inl, Matrix.fromBlocks_apply₁₁]
    exact h00 a b
  · rw [blockEquiv_inl, blockEquiv_inr, Matrix.fromBlocks_apply₁₂]
    exact h01 a b
  · rw [blockEquiv_inr, blockEquiv_inl, Matrix.fromBlocks_apply₂₁]
    exact h10 a b
  · rw [blockEquiv_inr, blockEquiv_inr, Matrix.fromBlocks_apply₂₂]
    exact h11 a b

/-- The Levi embedding is block diagonal in block coordinates. -/
theorem leviEmbedding_val (L : (succBlockShape m h).Levi R) :
    ((succBlockShape m h).leviEmbedding R L).val =
      Matrix.reindex (blockEquiv h) (blockEquiv h)
        (Matrix.fromBlocks (L 0).val 0 0 (L 1).val) :=
  val_eq_reindex_fromBlocks h
    (fun a b => (succBlockShape m h).leviEmbedding_apply_same R L 0 a b)
    (fun a b => leviEmbedding_index_zero_one h L a b)
    (fun a b => leviEmbedding_index_one_zero h L a b)
    (fun a b => (succBlockShape m h).leviEmbedding_apply_same R L 1 a b)

/-- The upper radical is `[[1, x], [0, 1]]` in block coordinates. -/
theorem upperRadical_val (x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) R) :
    (upperRadical h R x).val =
      Matrix.reindex (blockEquiv h) (blockEquiv h) (Matrix.fromBlocks 1 x 0 1) :=
  val_eq_reindex_fromBlocks h
    (fun a b => by rw [upperRadical_index_zero_zero, Matrix.one_apply])
    (fun a b => upperRadical_index_zero_one h R x a b)
    (fun a b => upperRadical_index_one_zero h R x a b)
    (fun a b => by rw [upperRadical_index_one_one, Matrix.one_apply])

theorem reindex_mul_reindex {n₀ n₁ : ℕ} (e : Fin n₀ ⊕ Fin n₁ ≃ Fin (t + 1))
    (M N : Matrix (Fin n₀ ⊕ Fin n₁) (Fin n₀ ⊕ Fin n₁) R) :
    Matrix.reindex e e M * Matrix.reindex e e N = Matrix.reindex e e (M * N) := by
  simp only [Matrix.reindex_apply]
  exact Matrix.submatrix_mul_equiv M N _ _ _

/-- The point `(L, x) ↦ leviEmbedding L * upperRadical x` of the upper two-block parabolic. -/
def parabolicPoint (p : (succBlockShape m h).Levi R × Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) R) :
    GeneralLinear (t + 1) R :=
  (succBlockShape m h).leviEmbedding R p.1 * upperRadical h R p.2

/-- The matrix of `parabolicPoint (L, x)` is `[[a, a * x], [0, d]]`. -/
theorem parabolicPoint_val (L : (succBlockShape m h).Levi R)
    (x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) R) :
    (parabolicPoint h (L, x)).val =
      Matrix.reindex (blockEquiv h) (blockEquiv h)
        (Matrix.fromBlocks (L 0).val ((L 0).val * x) 0 (L 1).val) := by
  rw [parabolicPoint, Units.val_mul, leviEmbedding_val, upperRadical_val, reindex_mul_reindex,
    Matrix.fromBlocks_multiply]
  simp

/-- Conjugating the upper radical by the Levi: `u(y) m = m u(a⁻¹ y d)`. -/
theorem upperRadical_mul_leviEmbedding (L : (succBlockShape m h).Levi R)
    (y : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) R) :
    upperRadical h R y * (succBlockShape m h).leviEmbedding R L =
      (succBlockShape m h).leviEmbedding R L *
        upperRadical h R (((L 0)⁻¹ : GeneralLinear (m 0 + 1) R).val * y * (L 1).val) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, leviEmbedding_val, upperRadical_val, upperRadical_val,
    reindex_mul_reindex, reindex_mul_reindex, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply]
  congr 2
  · simp
  · simp only [Matrix.mul_zero, add_zero, zero_add, Matrix.mul_one]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, Matrix.one_mul]
  · simp
  · simp

/-- Left translation in parabolic coordinates. -/
theorem parabolicPoint_inv_mul (L₀ L : (succBlockShape m h).Levi R)
    (x₀ x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) R) :
    (parabolicPoint h (L₀, x₀))⁻¹ * parabolicPoint h (L, x) =
      parabolicPoint h (L₀⁻¹ * L,
        x - (((L₀⁻¹ * L) 0)⁻¹ : GeneralLinear (m 0 + 1) R).val * x₀ * ((L₀⁻¹ * L) 1).val) := by
  simp only [parabolicPoint, mul_inv_rev, map_mul, map_inv]
  rw [sub_eq_neg_add, upperRadical_add, ← upperRadical_neg]
  have hc := upperRadical_mul_leviEmbedding h (L₀⁻¹ * L) (-x₀)
  rw [map_mul, map_inv] at hc
  rw [Matrix.mul_neg, Matrix.neg_mul] at hc
  simp only [mul_assoc]
  rw [← mul_assoc ((succBlockShape m h).leviEmbedding R L₀)⁻¹, ← mul_assoc, hc]
  simp only [mul_assoc]

/-- The upper-right block of a matrix, in block coordinates. -/
def corner (g : GeneralLinear (t + 1) R) : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) R :=
  fun a b => g ((succBlockShape m h).index 0 a) ((succBlockShape m h).index 1 b)

theorem parabolicPoint_mem (z : (succBlockShape m h).Levi R × Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) R) :
    parabolicPoint h z ∈ (succBlockShape m h).parabolic R := by
  rw [BlockShape.mem_parabolic_iff]
  intro i j a b hij
  have hi : i = 1 := by
    fin_cases i
    · exact absurd hij (by simp)
    · rfl
  have hj : j = 0 := by
    fin_cases j
    · rfl
    · subst hi; exact absurd hij (by simp)
  subst hi hj
  obtain ⟨L, x⟩ := z
  change (parabolicPoint h (L, x)).val _ _ = 0
  rw [parabolicPoint_val, ← blockEquiv_inr, ← blockEquiv_inl, Matrix.reindex_apply,
    Matrix.submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply,
    Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]

/-- Coordinates of an element of the upper two-block parabolic. -/
def parabolicCoord (q : (succBlockShape m h).parabolic R) :
    (succBlockShape m h).Levi R × Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) R :=
  ((succBlockShape m h).leviProjection R q,
    (((succBlockShape m h).leviProjection R q 0)⁻¹ : GeneralLinear (m 0 + 1) R).val *
      corner h q.val)

theorem parabolicPoint_parabolicCoord (q : (succBlockShape m h).parabolic R) :
    parabolicPoint h (parabolicCoord h q) = q.val := by
  apply Units.ext
  have hq : ∀ (a : Fin (m 1 + 1)) (b : Fin (m 0 + 1)),
      q.val ((succBlockShape m h).index 1 a) ((succBlockShape m h).index 0 b) = 0 :=
    fun a b => ((succBlockShape m h).mem_parabolic_iff R q.val).mp q.property 1 0 a b
      (show (0 : Fin 2) < 1 by decide)
  rw [parabolicCoord, parabolicPoint_val, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel,
    Units.val_one, Matrix.one_mul]
  symm
  exact val_eq_reindex_fromBlocks h (fun a b => rfl) (fun a b => rfl) (fun a b => hq a b)
    (fun a b => rfl)

theorem parabolicCoord_parabolicPoint
    (z : (succBlockShape m h).Levi R × Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) R) :
    parabolicCoord h ⟨parabolicPoint h z, parabolicPoint_mem h z⟩ = z := by
  obtain ⟨L, x⟩ := z
  have hval := parabolicPoint_val h L x
  have hentry : ∀ (s s' : Fin (m 0 + 1) ⊕ Fin (m 1 + 1)),
      (parabolicPoint h (L, x)) (blockEquiv h s) (blockEquiv h s') =
        Matrix.fromBlocks (L 0).val ((L 0).val * x) 0 (L 1).val s s' := by
    intro s s'
    rw [hval, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
      Equiv.symm_apply_apply]
  have h0 : (succBlockShape m h).leviProjection R
      ⟨parabolicPoint h (L, x), parabolicPoint_mem h _⟩ 0 = L 0 := by
    apply Units.ext
    ext a b
    rw [BlockShape.leviProjection_apply]
    change (parabolicPoint h (L, x)) ((succBlockShape m h).index 0 a)
      ((succBlockShape m h).index 0 b) = _
    rw [← blockEquiv_inl, ← blockEquiv_inl, hentry, Matrix.fromBlocks_apply₁₁]
  have h1 : (succBlockShape m h).leviProjection R
      ⟨parabolicPoint h (L, x), parabolicPoint_mem h _⟩ 1 = L 1 := by
    apply Units.ext
    ext a b
    rw [BlockShape.leviProjection_apply]
    change (parabolicPoint h (L, x)) ((succBlockShape m h).index 1 a)
      ((succBlockShape m h).index 1 b) = _
    rw [← blockEquiv_inr, ← blockEquiv_inr, hentry, Matrix.fromBlocks_apply₂₂]
  have hL : (succBlockShape m h).leviProjection R ⟨parabolicPoint h (L, x), parabolicPoint_mem h _⟩
      = L := by
    funext i
    fin_cases i
    · exact h0
    · exact h1
  have hc : corner h (parabolicPoint h (L, x)) = (L 0).val * x := by
    ext a b
    change (parabolicPoint h (L, x)) ((succBlockShape m h).index 0 a)
      ((succBlockShape m h).index 1 b) = _
    rw [← blockEquiv_inl, ← blockEquiv_inr, hentry, Matrix.fromBlocks_apply₁₂]
  rw [parabolicCoord, hL, hc, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel,
    Units.val_one, Matrix.one_mul]

/-- Every element of the upper two-block parabolic is a `parabolicPoint`. -/
theorem exists_parabolicPoint_eq (q : (succBlockShape m h).parabolic R) :
    ∃ z, parabolicPoint h z = q.val :=
  ⟨parabolicCoord h q, parabolicPoint_parabolicCoord h q⟩

theorem det_parabolicPoint (L : (succBlockShape m h).Levi R)
    (x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) R) :
    (parabolicPoint h (L, x)).val.det = (L 0).val.det * (L 1).val.det := by
  rw [parabolicPoint_val, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]

/-- A factorization `G = P K` gives a factorization through parabolic points. -/
theorem exists_parabolicPoint_mul (K : Subgroup (GeneralLinear (t + 1) R))
    (hPK : ∀ g : GeneralLinear (t + 1) R, ∃ (q : (succBlockShape m h).parabolic R) (k : K),
      g = (q : GeneralLinear (t + 1) R) * (k : GeneralLinear (t + 1) R)) (y : GeneralLinear (t + 1) R) :
    ∃ z, ∃ k ∈ K, y = parabolicPoint h z * k := by
  obtain ⟨q, k, rfl⟩ := hPK y
  exact ⟨parabolicCoord h q, k, k.property, by rw [parabolicPoint_parabolicCoord]⟩

/-- Left translation by `(parabolicPoint z₀)⁻¹` in parabolic coordinates. -/
def parabolicShift (z₀ z : (succBlockShape m h).Levi R × Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) R) :
    (succBlockShape m h).Levi R × Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) R :=
  (z₀.1⁻¹ * z.1, z.2 - (((z₀.1⁻¹ * z.1) 0)⁻¹ : GeneralLinear (m 0 + 1) R).val * z₀.2 *
    ((z₀.1⁻¹ * z.1) 1).val)

theorem parabolicPoint_parabolicShift
    (z₀ z : (succBlockShape m h).Levi R × Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) R) :
    parabolicPoint h (parabolicShift h z₀ z) = (parabolicPoint h z₀)⁻¹ * parabolicPoint h z :=
  (parabolicPoint_inv_mul h z₀.1 z.1 z₀.2 z.2).symm

@[simp] theorem parabolicPoint_one_zero : parabolicPoint h ((1, 0) :
    (succBlockShape m h).Levi R × Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) R) = 1 := by
  simp [parabolicPoint]

end Algebra

section Topology

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1) (R : Type uR) [CommRing R]
  [TopologicalSpace R] [IsTopologicalRing R]

theorem continuous_parabolicPoint : Continuous (parabolicPoint h (R := R)) :=
  (((succBlockShape m h).leviEmbeddingContinuous R).continuous.comp continuous_fst).mul
    ((continuous_upperRadical h R).comp continuous_snd)

omit [IsTopologicalRing R] in
theorem continuous_corner : Continuous (corner h (R := R)) :=
  continuous_pi fun _ => continuous_pi fun _ =>
    (Units.continuous_val (M := Matrix (Fin (t + 1)) (Fin (t + 1)) R)).matrix_elem _ _

theorem continuous_parabolicCoord : Continuous (parabolicCoord h (R := R)) := by
  have hlev : Continuous fun q : (succBlockShape m h).parabolic R =>
      (succBlockShape m h).leviProjection R q :=
    ((succBlockShape m h).leviProjectionContinuous R).continuous
  refine hlev.prodMk ?_
  exact (Units.continuous_val.comp (continuous_inv.comp
    ((continuous_apply (0 : Fin 2)).comp hlev))).matrix_mul
    ((continuous_corner h R).comp continuous_subtype_val)

end Topology

section Measure

open scoped ENNReal

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance : MeasurableSpace F.Carrier := borel _
local instance : BorelSpace F.Carrier := ⟨rfl⟩
local instance (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := borel _
local instance (n : ℕ) : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩

local instance glSecondCountable (n : ℕ) :
    SecondCountableTopology (Langlands.GeneralLinear n F.Carrier) := by
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) F.Carrier) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → F.Carrier))
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) F.Carrier)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isInducing_embedProduct.secondCountableTopology

local instance matrixLocallyCompact (r s : ℕ) :
    LocallyCompactSpace (Matrix (Fin r) (Fin s) F.Carrier) :=
  inferInstanceAs (LocallyCompactSpace (Fin r → Fin s → F.Carrier))

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

/-- The parameter measure `dL × dx` on `Levi × Mat_{(m 0 + 1) × (m 1 + 1)}`, with the
normalized Haar measures of the blocks and a supplied measure `dx` on the radical. -/
def parabolicMeasure (dx : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier)) :
    Measure ((succBlockShape m h).Levi F.Carrier ×
      Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier) :=
  (Measure.pi fun i : Fin 2 => generalLinearHaar F.Carrier (m i)).prod dx

local instance matrixSecondCountable (r s : ℕ) :
    SecondCountableTopology (Matrix (Fin r) (Fin s) F.Carrier) :=
  inferInstanceAs (SecondCountableTopology (Fin r → Fin s → F.Carrier))

local instance glLocallyCompact (n : ℕ) :
    LocallyCompactSpace (Langlands.GeneralLinear n F.Carrier) :=
  inferInstance

theorem measurable_parabolicPoint :
    Measurable (parabolicPoint h (R := F.Carrier)) :=
  (continuous_parabolicPoint h F.Carrier).measurable

variable (dx : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier))
  [dx.IsAddHaarMeasure]

instance parabolicMeasure_sigmaFinite : SigmaFinite (parabolicMeasure F h dx) := by
  unfold parabolicMeasure
  infer_instance

instance parabolicMeasure_isOpenPosMeasure : (parabolicMeasure F h dx).IsOpenPosMeasure := by
  unfold parabolicMeasure
  infer_instance

instance parabolicMeasure_isFiniteMeasureOnCompacts :
    IsFiniteMeasureOnCompacts (parabolicMeasure F h dx) := by
  unfold parabolicMeasure
  infer_instance

/-- Left translations of the parabolic are measure-preserving in parabolic coordinates. -/
theorem measurePreserving_parabolicShift
    (z₀ : (succBlockShape m h).Levi F.Carrier × Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier) :
    MeasurePreserving (parabolicShift h z₀) (parabolicMeasure F h dx) (parabolicMeasure F h dx) := by
  let c : (succBlockShape m h).Levi F.Carrier → Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier :=
    fun L => (((z₀.1⁻¹ * L) 0)⁻¹ : GeneralLinear (m 0 + 1) F.Carrier).val * z₀.2 *
      ((z₀.1⁻¹ * L) 1).val
  have hc : Continuous c := by
    have hL : Continuous fun L : (succBlockShape m h).Levi F.Carrier => z₀.1⁻¹ * L :=
      continuous_const.mul continuous_id
    exact ((Units.continuous_val.comp (continuous_inv.comp
      ((continuous_apply (0 : Fin 2)).comp hL))).matrix_mul continuous_const).matrix_mul
      (Units.continuous_val.comp ((continuous_apply (1 : Fin 2)).comp hL))
  have hg : Measurable (Function.uncurry fun (L : (succBlockShape m h).Levi F.Carrier)
      (x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier) => x - c L) :=
    (continuous_snd.sub (hc.comp continuous_fst)).measurable
  exact MeasurePreserving.skew_product (g := fun L x => x - c L)
    (measurePreserving_mul_left (Measure.pi fun i : Fin 2 => generalLinearHaar F.Carrier (m i))
      z₀.1⁻¹) hg
    (Filter.Eventually.of_forall fun L => map_sub_right_eq_self dx _)

/-- The parameter-space form of left translation required by the factorization integral. -/
theorem parabolicPoint_translation
    (z₀ : (succBlockShape m h).Levi F.Carrier × Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier) :
    ∃ σ, MeasurePreserving σ (parabolicMeasure F h dx) (parabolicMeasure F h dx) ∧
      ∀ z, parabolicPoint h (σ z) = (parabolicPoint h z₀)⁻¹ * parabolicPoint h z :=
  ⟨parabolicShift h z₀, measurePreserving_parabolicShift F h dx z₀,
    parabolicPoint_parabolicShift h z₀⟩

/-- The parameters of an open subgroup have positive measure. -/
theorem parabolicMeasure_preimage_ne_zero (K : OpenSubgroup (GeneralLinear (t + 1) F.Carrier)) :
    parabolicMeasure F h dx (parabolicPoint h ⁻¹' (K : Set (GeneralLinear (t + 1) F.Carrier))) ≠
      0 :=
  (K.isOpen.preimage (continuous_parabolicPoint h F.Carrier)).measure_ne_zero _
    ⟨(1, 0), by simp⟩

/-- The parameters of a compact subgroup have finite measure. -/
theorem parabolicMeasure_preimage_ne_top (K : Subgroup (GeneralLinear (t + 1) F.Carrier))
    (hK : IsCompact (K : Set (GeneralLinear (t + 1) F.Carrier))) :
    parabolicMeasure F h dx (parabolicPoint h ⁻¹' (K : Set (GeneralLinear (t + 1) F.Carrier))) ≠
      ∞ := by
  have hc : IsCompact (parabolicCoord h '' ((Subtype.val :
      (succBlockShape m h).parabolic F.Carrier → GeneralLinear (t + 1) F.Carrier) ⁻¹'
        (K : Set (GeneralLinear (t + 1) F.Carrier)))) :=
    (((succBlockShape m h).isClosed_parabolic F.Carrier).isClosedEmbedding_subtypeVal.isCompact_preimage
      hK).image (continuous_parabolicCoord h F.Carrier)
  have hsub : parabolicPoint h ⁻¹' (K : Set (GeneralLinear (t + 1) F.Carrier)) ⊆
      parabolicCoord h '' ((Subtype.val :
        (succBlockShape m h).parabolic F.Carrier → GeneralLinear (t + 1) F.Carrier) ⁻¹'
          (K : Set (GeneralLinear (t + 1) F.Carrier))) := by
    intro z hz
    exact ⟨⟨parabolicPoint h z, parabolicPoint_mem h z⟩, hz, parabolicCoord_parabolicPoint h z⟩
  exact (lt_of_le_of_lt (measure_mono hsub) hc.measure_lt_top).ne

section Scaling

open scoped NNReal

/-- Left multiplication by `a ∈ GL_(m 0 + 1)` scales the radical measure by `|det a|^(-(m 1 + 1))`. -/
theorem map_mul_left_radical (a : GeneralLinear (m 0 + 1) F.Carrier) :
    dx.map (fun x => a.val * x) =
      ((F.canonicalTopologicalData.determinantNorm (m 0 + 1) a : ℝ≥0) ^ (m 1 + 1))⁻¹ • dx := by
  have h := HarmonicAnalysis.padicRectangularHaarScaling F F.canonicalTopologicalData
    (m 0 + 1) (m 1 + 1) dx a 1
  have he : (fun X : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier =>
      (a : Matrix (Fin (m 0 + 1)) (Fin (m 0 + 1)) F.Carrier) * X *
        ((1⁻¹ : GeneralLinear (m 1 + 1) F.Carrier) : Matrix (Fin (m 1 + 1)) (Fin (m 1 + 1)) F.Carrier)) =
      fun X => a.val * X := by
    funext X
    simp
  rw [he, map_one, Units.val_one, one_pow, div_one] at h
  exact h

theorem measurableEmbedding_mul_left_radical (a : GeneralLinear (m 0 + 1) F.Carrier) :
    MeasurableEmbedding (fun x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier => a.val * x) := by
  refine MeasurableEmbedding.of_measurable_inverse
    (continuous_const.matrix_mul continuous_id).measurable ?_
    (g := fun x => (a⁻¹ : GeneralLinear (m 0 + 1) F.Carrier).val * x)
    (continuous_const.matrix_mul continuous_id).measurable ?_
  · have : Set.range (fun x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier => a.val * x) =
        Set.univ := by
      apply Set.eq_univ_of_forall
      intro y
      refine ⟨(a⁻¹ : GeneralLinear (m 0 + 1) F.Carrier).val * y, ?_⟩
      change a.val * ((a⁻¹ : GeneralLinear (m 0 + 1) F.Carrier).val * y) = y
      rw [← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
    rw [this]
    exact MeasurableSet.univ
  · intro x
    change (a⁻¹ : GeneralLinear (m 0 + 1) F.Carrier).val * (a.val * x) = x
    rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]

/-- **Radical scaling.** `∫ Ψ (a x) dx = |det a|^(-(m 1 + 1)) ∫ Ψ dx`. -/
theorem integral_mul_left_radical {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : GeneralLinear (m 0 + 1) F.Carrier) (Ψ : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier → E) :
    ∫ x, Ψ (a.val * x) ∂dx =
      (((F.canonicalTopologicalData.determinantNorm (m 0 + 1) a : ℝ≥0) : ℝ) ^ (m 1 + 1))⁻¹ •
        ∫ y, Ψ y ∂dx := by
  rw [← (measurableEmbedding_mul_left_radical F a).integral_map, map_mul_left_radical,
    integral_smul_nnreal_measure]
  rw [NNReal.smul_def]
  push_cast
  rfl

/-- Integrability is unchanged by the radical scaling. -/
theorem integrable_mul_left_radical_iff {E : Type*} [NormedAddCommGroup E]
    (a : GeneralLinear (m 0 + 1) F.Carrier) (Ψ : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier → E) :
    Integrable (fun x => Ψ (a.val * x)) dx ↔ Integrable Ψ dx := by
  change Integrable (Ψ ∘ fun x => a.val * x) dx ↔ _
  rw [← (measurableEmbedding_mul_left_radical F a).integrable_map_iff, map_mul_left_radical,
    ENNReal.smul_def]
  refine integrable_smul_measure ?_ ?_
  · simp
  · simp

end Scaling

section Factorization

variable (K : OpenSubgroup (GeneralLinear (t + 1) F.Carrier))
  (hK : IsCompact (K : Set (GeneralLinear (t + 1) F.Carrier)))
  (hPK : ∀ g : GeneralLinear (t + 1) F.Carrier,
    ∃ (q : (succBlockShape m h).parabolic F.Carrier) (k : K),
      g = (q : GeneralLinear (t + 1) F.Carrier) * (k : GeneralLinear (t + 1) F.Carrier))
include hK hPK

/-- **Parabolic integration formula, integrability.** For `G = P K`, a function on
`GL_(t+1)` is integrable exactly when `(k, z) ↦ f (parabolicPoint z * k)` is integrable
for `μ|_K × (dL × dx)`. -/
theorem integrable_parabolic_iff {E : Type*} [NormedAddCommGroup E]
    {f : GeneralLinear (t + 1) F.Carrier → E}
    (hf : AEStronglyMeasurable f (generalLinearHaar F.Carrier t)) :
    Integrable (fun q : GeneralLinear (t + 1) F.Carrier × ((succBlockShape m h).Levi F.Carrier ×
        Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier) => f (parabolicPoint h q.2 * q.1))
      (((generalLinearHaar F.Carrier t).restrict (K : Set (GeneralLinear (t + 1) F.Carrier))).prod
        (parabolicMeasure F h dx)) ↔
      Integrable f (generalLinearHaar F.Carrier t) :=
  CompactFactorization.integrable_comp_mul_iff (generalLinearHaar F.Carrier t) K.toSubgroup
    K.isOpen.measurableSet (parabolicMeasure F h dx) (parabolicPoint h)
    (measurable_parabolicPoint F h) (exists_parabolicPoint_mul h K.toSubgroup hPK)
    (parabolicPoint_translation F h dx) (parabolicMeasure_preimage_ne_zero F h dx K)
    (parabolicMeasure_preimage_ne_top F h dx K.toSubgroup hK) hf

/-- **Parabolic integration formula.** For `G = P K` with `K` compact open, the
`K`-integral of the parabolic-coordinate integrals of right translates is the
constant `(dL × dx) (parabolicPoint ⁻¹' K)` times the Haar integral. -/
theorem integral_parabolic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : GeneralLinear (t + 1) F.Carrier → E} (hf : Integrable f (generalLinearHaar F.Carrier t)) :
    ∫ k in (K : Set (GeneralLinear (t + 1) F.Carrier)),
        ∫ z, f (parabolicPoint h z * k) ∂(parabolicMeasure F h dx) ∂(generalLinearHaar F.Carrier t) =
      (parabolicMeasure F h dx (parabolicPoint h ⁻¹' (K : Set (GeneralLinear (t + 1) F.Carrier)))).toReal •
        ∫ g, f g ∂(generalLinearHaar F.Carrier t) :=
  CompactFactorization.integral_restrict_integral_mul (generalLinearHaar F.Carrier t) K.toSubgroup
    K.isOpen.measurableSet (parabolicMeasure F h dx) (parabolicPoint h)
    (measurable_parabolicPoint F h) (exists_parabolicPoint_mul h K.toSubgroup hPK)
    (parabolicPoint_translation F h dx) (parabolicMeasure_preimage_ne_zero F h dx K)
    (parabolicMeasure_preimage_ne_top F h dx K.toSubgroup hK) hf

end Factorization

end Measure

end Langlands.GodementJacquet.TwoBlock
