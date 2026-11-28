import Langlands.Representation.Shahidi.OpenCellCount
import Langlands.Representation.RankinSelberg.TwoBlockJacquetConvergence.BoxIntegrability

/-! # Integrals of lattice-periodic functions on rectangular matrix spaces

The additive Haar measure on a `p`-adic field normalized by `vol(𝒪) = 1` and its product on
`M_(a×b)(K)`. A function that is invariant under translation by `M_(a×b)(𝒪)` is locally
constant, and its integral is the sum of its values over the classes of `M_(a×b)(K)/M_(a×b)(𝒪)`
whenever that sum converges absolutely. -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Shahidi.OpenCell

open Langlands.GeneralLinear MeasureTheory
open scoped ENNReal NNReal

universe u

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{u} p)

local instance ocHaarTopologicalSpace : TopologicalSpace K.Carrier := K.canonicalTopologicalData.topology
local instance ocHaarValuativeRel : ValuativeRel K.Carrier := K.canonicalTopologicalData.valuativeRel
local instance ocHaarIsNonarchimedeanLocalField : IsNonarchimedeanLocalField K.Carrier := K.canonicalTopologicalData.localField
local instance ocHaarTSpace : T2Space K.Carrier := K.canonicalTopologicalData.fieldT2
local instance ocHaarSecondCountableTopology : SecondCountableTopology K.Carrier :=
  K.canonicalTopologicalData.secondCountableTopology
local instance ocHaarMeasurableSpace : MeasurableSpace K.Carrier := borel K.Carrier
local instance ocHaarBorelSpace : BorelSpace K.Carrier := ⟨rfl⟩

/-- The ring of integers as a positive compact set. -/
def integersCompacts : TopologicalSpace.PositiveCompacts K.Carrier where
  carrier := K.canonicalTopologicalData.Integers
  isCompact' := K.canonicalTopologicalData.isCompact_integers
  interior_nonempty' := by
    rw [K.canonicalTopologicalData.isOpen_integers.interior_eq]
    exact ⟨0, zero_mem _⟩

/-- The additive Haar measure on `K` with `vol(𝒪) = 1`. -/
def haarK : HarmonicAnalysis.AdditiveHaarMeasure K.Carrier :=
  HarmonicAnalysis.normalizedAdditiveHaar K.Carrier (integersCompacts K)

theorem haarK_integers :
    (haarK K).measure (K.canonicalTopologicalData.Integers : Set K.Carrier) = 1 :=
  Measure.addHaarMeasure_self

instance haarK_sigmaFinite : SigmaFinite (haarK K).measure := inferInstance

/-- The product Haar measure on `M_(a×b)(K)`. -/
def matrixHaar (a b : ℕ) : Measure (Matrix (Fin a) (Fin b) K.Carrier) :=
  RankinSelberg.rectangularMeasure (haarK K) a b

instance matrixHaar_isAddHaar (a b : ℕ) : (matrixHaar K a b).IsAddHaarMeasure :=
  RankinSelberg.rectangularMeasure_isAddHaar (haarK K) a b

instance matrixHaar_sigmaFinite (a b : ℕ) : SigmaFinite (matrixHaar K a b) :=
  RankinSelberg.rectangularMeasure_sigmaFinite (haarK K) a b

theorem matrixHaar_integralMatrices (a b : ℕ) :
    matrixHaar K a b (integralMatrices K a b : Set (Matrix (Fin a) (Fin b) K.Carrier)) = 1 := by
  have h := RankinSelberg.rectangularMeasure_entries_one (haarK K) a b
    (K.canonicalTopologicalData.Integers : Set K.Carrier) (haarK_integers K)
  have e : (integralMatrices K a b : Set (Matrix (Fin a) (Fin b) K.Carrier)) =
      {x | ∀ i j, x i j ∈ (K.canonicalTopologicalData.Integers : Set K.Carrier)} := by
    ext Y
    exact mem_integralMatrices_iff K a b Y
  rw [e]
  exact h

section Periodic

variable {a b : ℕ}

/-- Invariance under translation by the integral matrices. -/
def IsLatticePeriodic (G : Matrix (Fin a) (Fin b) K.Carrier → ℂ) : Prop :=
  ∀ Y Z, Z ∈ integralMatrices K a b → G (Y + Z) = G Y

theorem isOpen_integralMatrices :
    IsOpen (integralMatrices K a b : Set (Matrix (Fin a) (Fin b) K.Carrier)) := by
  have e : (integralMatrices K a b : Set (Matrix (Fin a) (Fin b) K.Carrier)) =
      Set.univ.pi fun _ : Fin a => Set.univ.pi fun _ : Fin b =>
        (K.canonicalTopologicalData.Integers : Set K.Carrier) := by
    ext Y
    rw [SetLike.mem_coe, mem_integralMatrices_iff]
    exact ⟨fun h i _ j _ => h i j, fun h i j => h i trivial j trivial⟩
  rw [e]
  exact isOpen_set_pi Set.finite_univ fun _ _ =>
    isOpen_set_pi Set.finite_univ fun _ _ => K.canonicalTopologicalData.isOpen_integers

/-- The class of `Y` as a subset. -/
theorem preimage_mk_eq (y : Matrix (Fin a) (Fin b) K.Carrier ⧸ integralMatrices K a b) :
    (QuotientAddGroup.mk ⁻¹' {y} : Set (Matrix (Fin a) (Fin b) K.Carrier)) =
      (fun Z => -Quotient.out y + Z) ⁻¹' (integralMatrices K a b : Set _) := by
  ext Z
  simp only [Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe]
  rw [← QuotientAddGroup.eq]
  constructor
  · intro h
    rw [h]
    exact Quotient.out_eq y
  · intro h
    rw [← h]
    exact Quotient.out_eq y

theorem isOpen_preimage_mk (y : Matrix (Fin a) (Fin b) K.Carrier ⧸ integralMatrices K a b) :
    IsOpen (QuotientAddGroup.mk ⁻¹' {y} : Set (Matrix (Fin a) (Fin b) K.Carrier)) := by
  rw [preimage_mk_eq]
  exact (isOpen_integralMatrices K).preimage (continuous_const.add continuous_id)

theorem matrixHaar_preimage_mk (y : Matrix (Fin a) (Fin b) K.Carrier ⧸ integralMatrices K a b) :
    matrixHaar K a b (QuotientAddGroup.mk ⁻¹' {y}) = 1 := by
  rw [preimage_mk_eq, measure_preimage_add, matrixHaar_integralMatrices]

theorem continuous_of_isLatticePeriodic {G : Matrix (Fin a) (Fin b) K.Carrier → ℂ}
    (hG : IsLatticePeriodic K G) : Continuous G := by
  apply IsLocallyConstant.continuous
  rw [IsLocallyConstant.iff_eventually_eq]
  intro Y
  have hopen : IsOpen ((fun Z => -Y + Z) ⁻¹' (integralMatrices K a b : Set _)) :=
    (isOpen_integralMatrices K).preimage (continuous_const.add continuous_id)
  have hmem : Y ∈ (fun Z => -Y + Z) ⁻¹' (integralMatrices K a b : Set _) := by
    simp only [Set.mem_preimage, neg_add_cancel, SetLike.mem_coe]
    exact zero_mem _
  filter_upwards [hopen.mem_nhds hmem] with Z hZ
  have h := hG Y (-Y + Z) hZ
  rwa [add_neg_cancel_left] at h

instance countable_quotient :
    Countable (Matrix (Fin a) (Fin b) K.Carrier ⧸ integralMatrices K a b) := by
  have : TopologicalSpace.SeparableSpace (Matrix (Fin a) (Fin b) K.Carrier) :=
    inferInstanceAs (TopologicalSpace.SeparableSpace (Fin a → Fin b → K.Carrier))
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (Matrix (Fin a) (Fin b) K.Carrier)
  have hsurj : Function.Surjective (fun d : D =>
      (QuotientAddGroup.mk (d : Matrix (Fin a) (Fin b) K.Carrier) :
        Matrix (Fin a) (Fin b) K.Carrier ⧸ integralMatrices K a b)) := by
    intro y
    obtain ⟨d, hd1, hd2⟩ := hDd.inter_open_nonempty _ (isOpen_preimage_mk K y)
      ⟨Quotient.out y, by simp only [Set.mem_preimage, Set.mem_singleton_iff]; exact Quotient.out_eq y⟩
    exact ⟨⟨d, hd2⟩, hd1⟩
  have := hDc.to_subtype
  exact hsurj.countable

/-- **The integral of a lattice-periodic function is the sum over the classes.** -/
theorem integrable_and_hasSum_of_isLatticePeriodic {G : Matrix (Fin a) (Fin b) K.Carrier → ℂ}
    (hG : IsLatticePeriodic K G)
    (hs : Summable fun y : Matrix (Fin a) (Fin b) K.Carrier ⧸ integralMatrices K a b =>
      ‖G (Quotient.out y)‖) :
    Integrable G (matrixHaar K a b) ∧
      HasSum (fun y : Matrix (Fin a) (Fin b) K.Carrier ⧸ integralMatrices K a b =>
        G (Quotient.out y)) (∫ Y, G Y ∂matrixHaar K a b) := by
  set Q := Matrix (Fin a) (Fin b) K.Carrier ⧸ integralMatrices K a b
  set s : Q → Set (Matrix (Fin a) (Fin b) K.Carrier) := fun y => QuotientAddGroup.mk ⁻¹' {y}
  have hsm : ∀ y, MeasurableSet (s y) := fun y => (isOpen_preimage_mk K y).measurableSet
  have hdisj : Pairwise (Function.onFun Disjoint s) := by
    intro y y' hyy'
    exact Set.disjoint_left.2 fun Z hZ hZ' => hyy' ((Set.mem_singleton_iff.1 hZ).symm.trans
      (Set.mem_singleton_iff.1 hZ'))
  have hunion : (⋃ y, s y) = Set.univ := by
    ext Z
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact ⟨QuotientAddGroup.mk Z, rfl⟩
  have hconst : ∀ y, ∀ Z ∈ s y, G Z = G (Quotient.out y) := by
    intro y Z hZ
    have hZ' : Z ∈ (fun Z => -Quotient.out y + Z) ⁻¹' (integralMatrices K a b : Set _) := by
      rwa [← preimage_mk_eq]
    have h := hG (Quotient.out y) (-Quotient.out y + Z) hZ'
    rwa [add_neg_cancel_left] at h
  have hint : ∀ y, ∫ Z in s y, G Z ∂matrixHaar K a b = G (Quotient.out y) := by
    intro y
    rw [setIntegral_congr_fun (hsm y) (fun Z hZ => hconst y Z hZ), setIntegral_const,
      measureReal_def, matrixHaar_preimage_mk, ENNReal.toReal_one, one_smul]
  have hnorm : ∀ y, ∫ Z in s y, ‖G Z‖ ∂matrixHaar K a b = ‖G (Quotient.out y)‖ := by
    intro y
    rw [setIntegral_congr_fun (hsm y) (fun Z hZ => by rw [hconst y Z hZ]), setIntegral_const,
      measureReal_def, matrixHaar_preimage_mk, ENNReal.toReal_one, one_smul]
  have hion : ∀ y, IntegrableOn G (s y) (matrixHaar K a b) := by
    intro y
    have hfin : matrixHaar K a b (s y) < ∞ := by
      rw [matrixHaar_preimage_mk]
      exact ENNReal.one_lt_top
    refine (integrableOn_const (C := G (Quotient.out y)) hfin.ne).congr_fun (fun Z hZ => ?_)
      (hsm y)
    rw [hconst y Z hZ]
  have hIU : IntegrableOn G (⋃ y, s y) (matrixHaar K a b) :=
    integrableOn_iUnion_of_summable_integral_norm hion (by simpa only [hnorm] using hs)
  rw [hunion, integrableOn_univ] at hIU
  refine ⟨hIU, ?_⟩
  have h := hasSum_integral_iUnion (f := G) (μ := matrixHaar K a b) hsm hdisj
    (by rw [hunion, integrableOn_univ]; exact hIU)
  rw [hunion, Measure.restrict_univ] at h
  simpa only [hint] using h

end Periodic

end Langlands.Shahidi.OpenCell
