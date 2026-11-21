import Langlands.BaseChange.ConcordanceRingEquiv
import Langlands.BaseChange.SplitContinuousMatching
import Langlands.TraceFormula.CyclicFieldGlobalizationStatement
import Langlands.TraceFormula.GeneralLinearBaseChangeLocal

/-! # Concordant tensor tests at a split infinite place -/

noncomputable section

namespace Langlands.TraceFormula

open MeasureTheory _root_.Topology
open Langlands.BaseChange Langlands.Global

universe u

variable (K L : Type u) [Field K] [Field L] [NumberField K] [Algebra K L]

set_option hygiene false in
local notation "A" => (placeCompletion K (.inl w) : Type u)

set_option hygiene false in
local notation "B" => LocalBaseChangeAlgebra K L (.inl w)

local instance (w : InfinitePlace K) : Field (placeCompletion K (.inl w)) :=
  inferInstanceAs (Field w.Completion)
local instance (w : InfinitePlace K) : IsTopologicalDivisionRing A :=
  inferInstanceAs (IsTopologicalDivisionRing w.Completion)

local instance {R : Type u} [CommRing R] [TopologicalSpace R] (n : ℕ) :
    MeasurableSpace (GeneralLinear n R) := borel _
local instance {R : Type u} [CommRing R] [TopologicalSpace R] (n : ℕ) :
    BorelSpace (GeneralLinear n R) := ⟨rfl⟩

/-- Apply the continuous splitting of the completed tensor algebra entrywise,
and then take the matrix group of each split factor. -/
def infiniteSplitMatrixCoordinates [FiniteDimensional K L]
    (w : InfinitePlace K) (n m : ℕ) (c : B ≃ₐ[A] (Fin (m + 1) → A)) :
    GeneralLinear n B ≃ₜ* (Fin (m + 1) → GeneralLinear n A) :=
  (generalLinearRingEquiv c.toRingEquiv
    (IsModuleTopology.continuous_of_linearMap c.toLinearMap)
    (IsModuleTopology.continuous_of_linearMap c.symm.toLinearMap)).trans
      (splitGLCoordinates A n (m + 1))

/-- Tensor and convolution matching in the actual completed tensor algebra
at a supplied split infinite place of a number-field extension. -/
def InfiniteSplitConcordanceStatement : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [NumberField K] [Algebra K L] [FiniteDimensional K L]
    (w : InfinitePlace K) (σ : L ≃ₐ[K] L) (n m : ℕ),
    IsCyclicShiftSplit K L A σ (m + 1) →
    ∀ (μF : Measure (GeneralLinear n A)) [μF.IsHaarMeasure]
      (ψ : Fin (m + 1) → GeneralLinear n A → ℂ),
      (∀ i, Continuous (ψ i)) → (∀ i, HasCompactSupport (ψ i)) →
      ∃ c : B ≃ₐ[A] (Fin (m + 1) → A),
        (∀ y : B, c (localGalois K L σ (.inl w) y) =
          fun i => c y (finRotate (m + 1) i)) ∧
        let κ := infiniteSplitMatrixCoordinates K L w n m c
        let μE := Measure.map κ.symm (Measure.pi fun _ : Fin (m + 1) => μF)
        let φ := fun x => ∏ i, ψ i (κ x i)
        let f := splitFiberConvolution μF ψ
        μE.IsHaarMeasure ∧
        (Continuous φ ∧ HasCompactSupport φ) ∧
        (Continuous f ∧ HasCompactSupport f) ∧
        AreConcordant (localGalois K L σ (.inl w)) (m + 1) μF μE φ f

set_option maxHeartbeats 850000 in
theorem infiniteSplitConcordance : InfiniteSplitConcordanceStatement.{u} := by
  intro K L _ _ _ _ _ w σ n m hsplit μF _ ψ hc hs
  obtain ⟨e, hShift⟩ := hsplit
  let c : B ≃ₐ[A] (Fin (m + 1) → A) := e
  have hshift (y : B) : c (localGalois K L σ (.inl w) y) =
      fun i => c y (finRotate (m + 1) i) := hShift y
  let : LocallyCompactSpace (Matrix (Fin n) (Fin n) A) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → A))
  let : LocallyCompactSpace (GeneralLinear n A) := inferInstance
  let : SecondCountableTopology A := infiniteCompletion_secondCountableTopology K w
  let : SecondCountableTopology (Matrix (Fin n) (Fin n) A) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → A))
  let : SecondCountableTopology (Matrix (Fin n) (Fin n) A)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  let : SecondCountableTopology (GeneralLinear n A) :=
    Units.isInducing_embedProduct.secondCountableTopology
  let cGL := generalLinearRingEquiv (n := n) c.toRingEquiv
    (IsModuleTopology.continuous_of_linearMap c.toLinearMap)
    (IsModuleTopology.continuous_of_linearMap c.symm.toLinearMap)
  let κ₀ := splitGLCoordinates A n (m + 1)
  let κ := infiniteSplitMatrixCoordinates K L w n m c
  let μE : Measure (GeneralLinear n B) := Measure.map κ.symm (Measure.pi fun _ : Fin (m + 1) => μF)
  let μSplit : Measure (GeneralLinear n (Fin (m + 1) → A)) := splitContinuousHaar (m := m) μF
  let φ₀ : GeneralLinear n (Fin (m + 1) → A) → ℂ := fun x => ∏ i, ψ i (κ₀ x i)
  let f := splitFiberConvolution μF ψ
  obtain ⟨_, hφ, hf, hMatch⟩ := splitContinuousMatching A n m μF ψ hc hs
  have hmap : Measure.map cGL μE = μSplit := by
    have he : Measurable (cGL : GeneralLinear n B → GeneralLinear n (Fin (m + 1) → A)) :=
      cGL.continuous.measurable
    have hκ : Measurable (κ.symm : (Fin (m + 1) → GeneralLinear n A) → GeneralLinear n B) :=
      κ.symm.continuous.measurable
    change Measure.map cGL (Measure.map κ.symm _) = _
    rw [Measure.map_map he hκ]
    have hcomp : cGL ∘ κ.symm = κ₀.symm := by
      funext x
      apply κ₀.injective
      exact κ.apply_symm_apply x
    exact congrArg (fun g => Measure.map g (Measure.pi fun _ : Fin (m + 1) => μF)) hcomp
  have hμE : Measure.map cGL.symm μSplit = μE :=
    hmap ▸ MeasurableEquiv.map_symm_map cGL.toHomeomorph.toMeasurableEquiv
  let : μSplit.IsHaarMeasure := splitContinuousHaar_isHaar μF
  have hE : μE.IsHaarMeasure := hμE ▸ cGL.symm.isHaarMeasure_map μSplit
  refine ⟨c, hshift, hE,
    ⟨hφ.1.comp cGL.continuous, hφ.2.comp_homeomorph cGL.toHomeomorph⟩, hf, ?_⟩
  have hLower : Measure.map
      (generalLinearRingEquiv (n := n) (RingEquiv.refl A) continuous_id continuous_id) μF = μF :=
    Measure.map_id
  have hMatch' : AreConcordant (splitCyclicShift A (m + 1)) (m + 1)
      (Measure.map (generalLinearRingEquiv (n := n) (RingEquiv.refl A) continuous_id continuous_id) μF)
      (Measure.map cGL μE) φ₀ f := by
    rw [hLower, hmap]
    exact hMatch
  exact areConcordant_pullback_ringEquiv (F := A) (E := B) (σ := localGalois K L σ (.inl w))
    (RingEquiv.refl A) c.toRingEquiv continuous_id continuous_id
    (IsModuleTopology.continuous_of_linearMap c.toLinearMap)
    (IsModuleTopology.continuous_of_linearMap c.symm.toLinearMap)
    (fun x => c.commutes x) (fun y => hshift y)
    (IsModuleTopology.continuous_of_linearMap (Algebra.linearMap A B))
    (IsModuleTopology.continuous_of_linearMap (Algebra.linearMap A (Fin (m + 1) → A)))
    μF μE φ₀ f hMatch'

end Langlands.TraceFormula
