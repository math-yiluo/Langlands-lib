import Langlands.TraceFormula.InfiniteSplitConcordance
import Langlands.TraceFormula.SplitSmoothingPowers

/-! # Concordance of smoothing powers at a split infinite place -/

noncomputable section

namespace Langlands.TraceFormula

open MeasureTheory
open Langlands.BaseChange Langlands.Global Langlands.Hecke

universe u

section ChangeOfVariables

variable {G H : Type*} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]
  [IsTopologicalGroup G] [IsTopologicalGroup H] [T2Space G] [T2Space H]
  [LocallyCompactSpace G] [LocallyCompactSpace H]
  [SecondCountableTopology G] [SecondCountableTopology H]
  [MeasurableSpace G] [MeasurableSpace H] [BorelSpace G] [BorelSpace H]

private theorem power_pullback (e : G ≃ₜ* H) (μ : Measure G) [μ.IsHaarMeasure]
    (ν : Measure H) [ν.IsHaarMeasure] (hμ : μ.map e = ν)
    (f : H → ℂ) (hc : Continuous f) (hs : HasCompactSupport f) (k : ℕ) :
    positiveConvolutionPower μ (f ∘ e) k = positiveConvolutionPower ν f k ∘ e := by
  induction k with
  | zero => simp only [positiveConvolutionPower_zero]
  | succ k ih =>
    rw [positiveConvolutionPower_succ μ (f := f ∘ e) (hc.comp e.continuous)
      (hs.comp_homeomorph e.toHomeomorph) k, ih, positiveConvolutionPower_succ ν hc hs k]
    funext x
    rw [convolutionIntegral_comp_continuousMulEquiv e, hμ]
    rfl

end ChangeOfVariables

variable (K L : Type u) [Field K] [Field L] [NumberField K] [Algebra K L]

set_option hygiene false in
local notation "A" => (placeCompletion K (.inl w) : Type u)

set_option hygiene false in
local notation "B" => LocalBaseChangeAlgebra K L (.inl w)

local instance (w : InfinitePlace K) : Field (placeCompletion K (.inl w)) :=
  inferInstanceAs (Field w.Completion)
local instance (w : InfinitePlace K) : IsTopologicalDivisionRing A :=
  inferInstanceAs (IsTopologicalDivisionRing w.Completion)

private local instance {R : Type u} [CommRing R] [TopologicalSpace R] (n : ℕ) :
    MeasurableSpace (GeneralLinear n R) := borel _
private local instance {R : Type u} [CommRing R] [TopologicalSpace R] (n : ℕ) :
    BorelSpace (GeneralLinear n R) := ⟨rfl⟩

/-- At a split infinite place, the identical-factor tensor test and its matching
ordered convolution remain concordant through the entire family of smoothing
powers with the same local Haar measures. -/
def InfiniteSplitSmoothingPowersStatement : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [NumberField K] [Algebra K L] [FiniteDimensional K L]
    (w : InfinitePlace K) (σ : L ≃ₐ[K] L) (n m : ℕ)
    (s : B ≃ₐ[A] (Fin (m + 1) → A)),
    (∀ y : B, s (localGalois K L σ (.inl w) y) =
      fun i => s y (finRotate (m + 1) i)) →
    ∀ (μF : Measure (GeneralLinear n A)) [μF.IsHaarMeasure]
      (f : GeneralLinear n A → ℂ), Continuous f → HasCompactSupport f →
      let κ := infiniteSplitMatrixCoordinates K L w n m s
      let μE := Measure.map κ.symm (Measure.pi fun _ : Fin (m + 1) => μF)
      let φ := fun x => ∏ i, f (κ x i)
      let b := positiveConvolutionPower μF f m
      μE.IsHaarMeasure ∧ (Continuous φ ∧ HasCompactSupport φ) ∧
        (Continuous b ∧ HasCompactSupport b) ∧
        ∀ k : ℕ, AreConcordant (localGalois K L σ (.inl w)) (m + 1) μF μE
          (positiveConvolutionPower μE φ k) (positiveConvolutionPower μF b k)

set_option maxHeartbeats 1100000 in
theorem infiniteSplitSmoothingPowers : InfiniteSplitSmoothingPowersStatement.{u} := by
  intro K L _ _ _ _ _ w σ n m s hshift μF _ f hfc hfs κ μE φ b
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
  let ρ := generalLinearRingEquiv (n := n) s.toRingEquiv
    (IsModuleTopology.continuous_of_linearMap s.toLinearMap)
    (IsModuleTopology.continuous_of_linearMap s.symm.toLinearMap)
  let e := splitGLCoordinates A n (m + 1)
  let μS : Measure (GeneralLinear n (Fin (m + 1) → A)) := splitContinuousHaar (m := m) μF
  let : μS.IsHaarMeasure := splitContinuousHaar_isHaar μF
  let : LocallyCompactSpace (GeneralLinear n (Fin (m + 1) → A)) :=
    e.toHomeomorph.isOpenEmbedding.locallyCompactSpace
  let : SecondCountableTopology (GeneralLinear n (Fin (m + 1) → A)) :=
    e.toHomeomorph.isInducing.secondCountableTopology
  let : LocallyCompactSpace (GeneralLinear n B) := κ.toHomeomorph.isOpenEmbedding.locallyCompactSpace
  let : SecondCountableTopology (GeneralLinear n B) :=
    κ.toHomeomorph.isInducing.secondCountableTopology
  let φS : GeneralLinear n (Fin (m + 1) → A) → ℂ := fun x => ∏ i, f (e x i)
  have hm : μE.map ρ = μS := by
    have hρ : Measurable (ρ : GeneralLinear n B → GeneralLinear n (Fin (m + 1) → A)) :=
      ρ.continuous.measurable
    have hκ : Measurable (κ.symm : (Fin (m + 1) → GeneralLinear n A) → GeneralLinear n B) :=
      κ.symm.continuous.measurable
    change Measure.map ρ (Measure.map κ.symm _) = _
    rw [Measure.map_map hρ hκ]
    have hcomp : ρ ∘ κ.symm = e.symm := by
      funext x
      apply e.injective
      exact κ.apply_symm_apply x
    rw [hcomp]
    rfl
  have hμE : μE.IsHaarMeasure :=
    (hm ▸ MeasurableEquiv.map_symm_map ρ.toHomeomorph.toMeasurableEquiv) ▸ ρ.symm.isHaarMeasure_map μS
  let := hμE
  have ⟨hφc, hφs⟩ := splitTensorInCoordinates_continuous_hasCompactSupport e (fun _ => f)
    (fun _ => hfc) (fun _ => hfs)
  refine ⟨hμE, ⟨hφc.comp ρ.continuous, hφs.comp_homeomorph ρ.toHomeomorph⟩,
    positiveConvolutionPower_continuous_hasCompactSupport μF hfc hfs m, fun k => ?_⟩
  have hMatch := splitSmoothingPowers A n m μF f hfc hfs k
  have hId : Measure.map
      (generalLinearRingEquiv (n := n) (RingEquiv.refl A) continuous_id continuous_id) μF = μF :=
    Measure.map_id
  have hMatch' : AreConcordant (splitCyclicShift A (m + 1)) (m + 1)
      (Measure.map (generalLinearRingEquiv (n := n) (RingEquiv.refl A)
        continuous_id continuous_id) μF)
      (Measure.map ρ μE) (positiveConvolutionPower μS φS k) (positiveConvolutionPower μF b k) := by
    rw [hId, hm]
    exact hMatch
  change AreConcordant (localGalois K L σ (.inl w)) (m + 1) μF μE
    (positiveConvolutionPower μE (φS ∘ ρ) k) (positiveConvolutionPower μF b k)
  rw [power_pullback ρ μE μS hm φS hφc hφs k]
  exact areConcordant_pullback_ringEquiv (F := A) (E := B) (σ := localGalois K L σ (.inl w))
    (RingEquiv.refl A) s.toRingEquiv continuous_id continuous_id
    (IsModuleTopology.continuous_of_linearMap s.toLinearMap)
    (IsModuleTopology.continuous_of_linearMap s.symm.toLinearMap)
    (fun x => s.commutes x) hshift
    (IsModuleTopology.continuous_of_linearMap (Algebra.linearMap A B))
    (IsModuleTopology.continuous_of_linearMap (Algebra.linearMap A (Fin (m + 1) → A)))
    μF μE _ _ hMatch'

end Langlands.TraceFormula
