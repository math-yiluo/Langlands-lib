import Langlands.Representation.RankinSelberg.TwoBlockDominantRectangleHaar

/-!
# Signed exchange of the two dominant rectangles

The coordinate map needed for the strictly dominant reversed-dual calculation
exchanges the rectangles and applies negative transpose with both indices reversed.
It preserves the exact product of every supplied additive Haar measure.
This module does not compare the large-group matrices or their scalar kernels.
-/

noncomputable section

namespace Langlands.RankinSelberg.TwoBlockDominantRectangular

open MeasureTheory HarmonicAnalysis

universe uF uE

section Coordinates

variable {K : Type uF} [AddCommGroup K]

/-- Negative transpose with reversal of the row and column coordinates. -/
def signedReverseTranspose (a b : ℕ) :
    Matrix (Fin b) (Fin a) K ≃+ Matrix (Fin a) (Fin b) K where
  toFun X i l := -X l.rev i.rev
  invFun X i l := -X l.rev i.rev
  left_inv X := by ext i l; simp
  right_inv X := by ext i l; simp
  map_add' X Y := by
    ext i l
    change -(X l.rev i.rev + Y l.rev i.rev) =
      -X l.rev i.rev + -Y l.rev i.rev
    exact neg_add _ _

@[simp] theorem signedReverseTranspose_apply (a b : ℕ)
    (X : Matrix (Fin b) (Fin a) K) (i : Fin a) (l : Fin b) :
    signedReverseTranspose a b X i l = -X l.rev i.rev := rfl

@[simp] theorem signedReverseTranspose_symm_apply (a b : ℕ)
    (X : Matrix (Fin a) (Fin b) K) (i : Fin b) (l : Fin a) :
    (signedReverseTranspose a b).symm X i l = -X l.rev i.rev := rfl

/-- Exchange the actual reversed rectangles, retaining every empty dimension.
The source order is `(b,j,1,k,a)` and the target order is `(a,k,1,j,b)`. -/
def dualRectangleEquiv (m : Fin 2 → ℕ) (j k : ℕ) :
    Rectangles (fun i => m i.rev) k j K ≃+ Rectangles m j k K where
  toFun z := (signedReverseTranspose (m 0 + 1) k z.2,
    signedReverseTranspose j (m 1 + 1) z.1)
  invFun z := (signedReverseTranspose (m 1 + 1) j z.2,
    signedReverseTranspose k (m 0 + 1) z.1)
  left_inv z := by ext i l <;> simp
  right_inv z := by ext i l <;> simp
  map_add' z w := by
    simp only [Prod.fst_add, Prod.snd_add, map_add, Prod.mk_add_mk]

@[simp] theorem dualRectangleEquiv_apply (m : Fin 2 → ℕ) (j k : ℕ)
    (x : Matrix (Fin (m 1 + 1)) (Fin j) K)
    (y : Matrix (Fin k) (Fin (m 0 + 1)) K) :
    dualRectangleEquiv m j k (x, y) =
      (signedReverseTranspose (m 0 + 1) k y,
        signedReverseTranspose j (m 1 + 1) x) := rfl

@[simp] theorem dualRectangleEquiv_symm_apply (m : Fin 2 → ℕ) (j k : ℕ)
    (x : Matrix (Fin (m 0 + 1)) (Fin k) K)
    (y : Matrix (Fin j) (Fin (m 1 + 1)) K) :
    (dualRectangleEquiv m j k).symm (x, y) =
      (signedReverseTranspose (m 1 + 1) j y,
        signedReverseTranspose k (m 0 + 1) x) := rfl

section Topology

variable [TopologicalSpace K] [ContinuousNeg K]

theorem continuous_signedReverseTranspose (a b : ℕ) :
    Continuous (signedReverseTranspose (K := K) a b) := by
  refine continuous_pi fun i => continuous_pi fun l => ?_
  change Continuous (fun X : Matrix (Fin b) (Fin a) K => -X l.rev i.rev)
  exact (continuous_apply_apply l.rev i.rev).neg

/-- The signed rectangle map has its explicit continuous inverse. -/
def signedReverseTransposeHomeomorph (a b : ℕ) :
    Matrix (Fin b) (Fin a) K ≃ₜ Matrix (Fin a) (Fin b) K where
  toEquiv := (signedReverseTranspose a b).toEquiv
  continuous_toFun := continuous_signedReverseTranspose a b
  continuous_invFun := continuous_signedReverseTranspose b a

/-- The actual signed exchange is a homeomorphism before any Haar choice. -/
def dualRectangleHomeomorph (m : Fin 2 → ℕ) (j k : ℕ) :
    Rectangles (fun i => m i.rev) k j K ≃ₜ Rectangles m j k K where
  toEquiv := (dualRectangleEquiv m j k).toEquiv
  continuous_toFun :=
    ((continuous_signedReverseTranspose _ _).comp continuous_snd).prodMk
      ((continuous_signedReverseTranspose _ _).comp continuous_fst)
  continuous_invFun :=
    ((continuous_signedReverseTranspose _ _).comp continuous_snd).prodMk
      ((continuous_signedReverseTranspose _ _).comp continuous_fst)

end Topology

end Coordinates

section ScalarMeasure

variable {K : Type uF} [AddCommGroup K] [MeasurableSpace K] [MeasurableNeg K]

theorem measurable_signedReverseTranspose (a b : ℕ) :
    Measurable (signedReverseTranspose (K := K) a b) :=
  Measurable.of_eval_matrix _ fun _ _ => Matrix.measurable_apply.neg

variable [TopologicalSpace K]

-- This cylinder proof generalizes the private `measurePreserving_rho` argument
-- in the published `TwoBlockDualSectionJacquetProof` to reusable coordinates.
theorem measurePreserving_signedReverseTranspose (ν : AdditiveHaarMeasure K)
    [SigmaFinite ν.measure] [Measure.IsNegInvariant ν.measure] (a b : ℕ) :
    MeasurePreserving (signedReverseTranspose (K := K) a b)
      (rectangularMeasure ν b a) (rectangularMeasure ν a b) := by
  refine ⟨measurable_signedReverseTranspose a b, ?_⟩
  symm
  refine Measure.pi_eq_generateFrom
    (C := fun _ : Fin a => Set.pi Set.univ '' Set.pi Set.univ
      fun _ : Fin b => {s : Set K | MeasurableSet s})
    (fun _ => generateFrom_pi) (fun _ => isPiSystem_pi)
    (fun _ => Measure.FiniteSpanningSetsIn.pi fun _ => ν.measure.toFiniteSpanningSetsIn) ?_
  intro S hS
  choose s hs hSs using hS
  obtain rfl : S = fun i => Set.pi Set.univ (s i) := funext fun i => (hSs i).symm
  have hmeas : MeasurableSet
      (Set.pi Set.univ (fun i => Set.pi Set.univ (s i)) :
        Set (Matrix (Fin a) (Fin b) K)) :=
    MeasurableSet.univ_pi fun i => MeasurableSet.univ_pi fun l => hs i l (Set.mem_univ l)
  have hmap := Measure.map_apply (μ := rectangularMeasure ν b a)
    (measurable_signedReverseTranspose a b) hmeas
  have hpre : signedReverseTranspose (K := K) a b ⁻¹'
      (Set.pi Set.univ (fun i => Set.pi Set.univ (s i)) :
        Set (Matrix (Fin a) (Fin b) K)) =
      Set.pi Set.univ (fun l : Fin b => Set.pi Set.univ
        (fun i : Fin a => (fun x : K => -x) ⁻¹' s i.rev l.rev)) := by
    ext X
    constructor
    · intro h l _ i _
      simpa only [Set.mem_preimage, signedReverseTranspose_apply, Fin.rev_rev]
        using h i.rev trivial l.rev trivial
    · intro h i _ l _
      simpa only [Set.mem_preimage, signedReverseTranspose_apply, Fin.rev_rev]
        using h l.rev trivial i.rev trivial
  refine hmap.trans ?_
  rw [hpre]
  change Measure.pi (fun _ : Fin b => Measure.pi (fun _ : Fin a => ν.measure)) _ = _
  simp only [Measure.pi_pi]
  have hn : ∀ i l, ν.measure ((fun x : K => -x) ⁻¹' s i l) = ν.measure (s i l) :=
    fun i l => (Measure.measurePreserving_neg ν.measure).measure_preimage
      ((hs i l trivial).nullMeasurableSet)
  simp only [hn]
  calc
    (∏ l : Fin b, ∏ i : Fin a, ν.measure (s i.rev l.rev)) =
        ∏ l : Fin b, ∏ i : Fin a, ν.measure (s i l) := by
      rw [← Equiv.prod_comp Fin.revPerm (fun l : Fin b => ∏ i : Fin a, ν.measure (s i l))]
      apply Finset.prod_congr rfl
      intro l _
      exact Equiv.prod_comp Fin.revPerm (fun i : Fin a => ν.measure (s i l.rev))
    _ = _ := Finset.prod_comm

end ScalarMeasure

section PadicMeasure

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance dualRectangleTopology : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance dualRectangleValuation : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance dualRectangleLocalField : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance dualRectangleSecondCountable : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance dualRectangleMeasurable : MeasurableSpace F.Carrier := borel F.Carrier
local instance dualRectangleBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance dualRectangleMatrixSecondCountable (a b : ℕ) :
    SecondCountableTopology (Matrix (Fin a) (Fin b) F.Carrier) :=
  inferInstanceAs (SecondCountableTopology (Fin a → Fin b → F.Carrier))
local instance dualRectangleMatrixBorel (a b : ℕ) :
    BorelSpace (Matrix (Fin a) (Fin b) F.Carrier) :=
  inferInstanceAs (BorelSpace (Fin a → Fin b → F.Carrier))
local instance dualRectangleProductBorel (m : Fin 2 → ℕ) (j k : ℕ) :
    BorelSpace (Rectangles m j k F.Carrier) :=
  inferInstanceAs (BorelSpace
    (Matrix (Fin (m 0 + 1)) (Fin k) F.Carrier ×
      Matrix (Fin j) (Fin (m 1 + 1)) F.Carrier))

/-- The signed rectangle exchange preserves the exact supplied product Haar.
No self-duality, nontrivial character, or positivity of `j,k` is required. -/
theorem measurePreserving_dualRectangleEquiv
    (m : Fin 2 → ℕ) (j k : ℕ) (ν : AdditiveHaarMeasure F.Carrier) :
    MeasurePreserving (dualRectangleEquiv (K := F.Carrier) m j k)
      (rectangleMeasure F (fun i => m i.rev) k j ν)
      (rectangleMeasure F m j k ν) := by
  have hx := measurePreserving_signedReverseTranspose ν (m 0 + 1) k
  have hy := measurePreserving_signedReverseTranspose ν j (m 1 + 1)
  exact (hx.prod hy).comp (Measure.measurePreserving_swap)

/-- The inverse preserves the same supplied products with their roles exchanged. -/
theorem measurePreserving_dualRectangleEquiv_symm
    (m : Fin 2 → ℕ) (j k : ℕ) (ν : AdditiveHaarMeasure F.Carrier) :
    MeasurePreserving (dualRectangleEquiv (K := F.Carrier) m j k).symm
      (rectangleMeasure F m j k ν)
      (rectangleMeasure F (fun i => m i.rev) k j ν) :=
  MeasurePreserving.symm (dualRectangleHomeomorph m j k).toMeasurableEquiv
    (measurePreserving_dualRectangleEquiv F m j k ν)

/-- Total Bochner change of variables for the two actual rectangle products. -/
theorem integral_dualRectangleEquiv
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (m : Fin 2 → ℕ) (j k : ℕ) (ν : AdditiveHaarMeasure F.Carrier)
    (φ : Rectangles m j k F.Carrier → E) :
    (∫ z, φ (dualRectangleEquiv m j k z)
      ∂rectangleMeasure F (fun i => m i.rev) k j ν) =
        ∫ z, φ z ∂rectangleMeasure F m j k ν :=
  (measurePreserving_dualRectangleEquiv F m j k ν).integral_comp
    (dualRectangleHomeomorph m j k).measurableEmbedding φ

/-- Absolute integrability is transported in both directions; it is not asserted. -/
theorem integrable_dualRectangleEquiv_iff
    {E : Type uE} [NormedAddCommGroup E]
    (m : Fin 2 → ℕ) (j k : ℕ) (ν : AdditiveHaarMeasure F.Carrier)
    (φ : Rectangles m j k F.Carrier → E) :
    Integrable (fun z => φ (dualRectangleEquiv m j k z))
        (rectangleMeasure F (fun i => m i.rev) k j ν) ↔
      Integrable φ (rectangleMeasure F m j k ν) :=
  (measurePreserving_dualRectangleEquiv F m j k ν).integrable_comp_emb
    (dualRectangleHomeomorph m j k).measurableEmbedding

end PadicMeasure

end Langlands.RankinSelberg.TwoBlockDominantRectangular
