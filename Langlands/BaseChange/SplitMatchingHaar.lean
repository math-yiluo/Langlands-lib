import Langlands.BaseChange.SplitMatchingStatement
import Langlands.Group.GL.LocalFieldTopology
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Topology.Algebra.Group.Units

/-! Product coordinates and the Haar normalization at a split place. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure

namespace Langlands.BaseChange

open HarmonicAnalysis (SchwartzBruhat)

universe u

section Coordinates

variable (F : Type u) [CommRing F] [TopologicalSpace F] (n m : ℕ)

/-- The topological group coordinates of the general linear group over a finite product. -/
def splitGLCoordinates : GeneralLinear n (Fin m → F) ≃ₜ* (Fin m → GeneralLinear n F) :=
  (Units.mapContinuousMulEquiv
    { toMulEquiv := (Matrix.piRingEquiv (β := fun _ : Fin m => F) (n := Fin n)).toMulEquiv
      continuous_toFun := continuous_pi fun i => continuous_pi fun a => continuous_pi fun b =>
        (continuous_apply i).comp ((continuous_apply b).comp (continuous_apply a))
      continuous_invFun := continuous_pi fun a => continuous_pi fun b => continuous_pi fun i =>
        (continuous_apply b).comp ((continuous_apply a).comp (continuous_apply i)) }).trans
    ContinuousMulEquiv.piUnits

@[simp] theorem splitGLCoordinates_apply (g : GeneralLinear n (Fin m → F)) (i : Fin m) :
    splitGLCoordinates F n m g i =
      Matrix.GeneralLinearGroup.map (Pi.evalRingHom (fun _ : Fin m => F) i) g := by
  ext a b
  rfl

@[simp] theorem splitGLCoordinates_baseChange (g : GeneralLinear n F) (i : Fin m) :
    splitGLCoordinates F n m (baseChange F (Fin m → F) n g) i = g := by
  rw [splitGLCoordinates_apply]
  ext a b
  rfl

@[simp] theorem splitGLCoordinates_shift (g : GeneralLinear n (Fin m → F)) (i : Fin m) :
    splitGLCoordinates F n m (entrywiseAut (splitCyclicShift F m) n g) i =
      splitGLCoordinates F n m g (finRotate m i) := by
  simp only [splitGLCoordinates_apply, map_evalRingHom_entrywiseAut_splitCyclicShift]

end Coordinates

section Measures

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {n m : ℕ}
  [MeasurableSpace (GeneralLinear n F)] [BorelSpace (GeneralLinear n F)]
  [MeasurableSpace (GeneralLinear n (Fin m → F))] [BorelSpace (GeneralLinear n (Fin m → F))]

local notation "G" => GeneralLinear n F
local notation "GE" => GeneralLinear n (Fin m → F)
local notation "κ" => splitGLCoordinates F n m

/-- The product Haar measure put on the actual group over the split algebra. -/
def splitProductMeasure (μ : Measure G) : Measure GE :=
  Measure.map (κ).symm (Measure.pi (fun _ : Fin m => μ))

theorem splitProductMeasure_isHaar (μ : Measure G) [μ.IsHaarMeasure] :
    (splitProductMeasure (m := m) μ).IsHaarMeasure := by
  let := LocalFieldTopology.generalLinear_secondCountableTopology F n
  let := LocalFieldTopology.generalLinear_locallyCompactSpace F n
  exact (κ).symm.isHaarMeasure_map _

theorem splitProductMeasure_isSplitProductHaar (μ : Measure G) [μ.IsHaarMeasure] :
    IsSplitProductHaar μ (splitProductMeasure (m := m) μ) := by
  let := LocalFieldTopology.generalLinear_secondCountableTopology F n
  let := LocalFieldTopology.generalLinear_locallyCompactSpace F n
  intro ψ
  let e := (κ).symm.toHomeomorph.toMeasurableEquiv
  change (∫ g, splitTensor (fun i => (ψ i : G → ℂ)) g
      ∂Measure.map e (Measure.pi (fun _ : Fin m => μ))) = _
  rw [integral_map_equiv e]
  change (∫ x, splitTensor (fun i => (ψ i : G → ℂ)) ((κ).symm x)
      ∂Measure.pi (fun _ : Fin m => μ)) = _
  simpa only [splitTensor_apply, ← splitGLCoordinates_apply, ContinuousMulEquiv.apply_symm_apply]
    using integral_fintype_prod_eq_prod (fun i => (ψ i : G → ℂ))

/-- Among Haar measures the split-tensor integrals determine the entire measure. -/
theorem eq_splitProductMeasure (μ : Measure G) [μ.IsHaarMeasure] (ν : Measure GE)
    [ν.IsHaarMeasure] (hν : IsSplitProductHaar μ ν) : ν = splitProductMeasure μ := by
  let := LocalFieldTopology.generalLinear_secondCountableTopology F n
  let := LocalFieldTopology.generalLinear_locallyCompactSpace F n
  let : LocallyCompactSpace GE := (κ).toHomeomorph.isClosedEmbedding.locallyCompactSpace
  let : SecondCountableTopology GE := (κ).toHomeomorph.secondCountableTopology
  let ν₀ : Measure GE := splitProductMeasure μ
  have : ν₀.IsHaarMeasure := splitProductMeasure_isHaar μ
  have h := isMulLeftInvariant_eq_smul ν ν₀
  obtain ⟨K, hK, -⟩ := LocalFieldTopology.generalLinear_compactOpen F n Set.univ Filter.univ_mem
  let ψ : SchwartzBruhat G :=
    ⟨(K : Set G).indicator (fun _ => 1),
      (LocallyConstant.indicator (LocallyConstant.const G (1 : ℂ))
        ⟨K.isClosed, K.isOpen⟩).isLocallyConstant,
      HasCompactSupport.intro' hK K.isClosed (fun _ hx => Set.indicator_of_notMem hx _)⟩
  have hψ : (∫ g, ψ g ∂μ) ≠ 0 := by
    change (∫ g, (K : Set G).indicator (fun _ => (1 : ℂ)) g ∂μ) ≠ 0
    rw [integral_indicator_const _ K.isOpen.measurableSet, Complex.real_smul, mul_one]
    exact_mod_cast ENNReal.toReal_ne_zero.mpr
      ⟨(K.isOpen.measure_pos μ ⟨1, K.one_mem⟩).ne', hK.measure_lt_top.ne⟩
  let f : GE → ℂ := splitTensor (fun _ : Fin m => (ψ : G → ℂ))
  have htest : (∫ x, f x ∂ν₀) ≠ 0 := by
    rw [show (∫ x, f x ∂ν₀) = ∏ _ : Fin m, ∫ g, ψ g ∂μ from
      splitProductMeasure_isSplitProductHaar μ (fun _ => ψ)]
    exact Finset.prod_ne_zero_iff.mpr (fun _ _ => hψ)
  have hi : (∫ x, f x ∂ν) = ∫ x, f x ∂ν₀ :=
    (hν (fun _ => ψ)).trans (splitProductMeasure_isSplitProductHaar μ (fun _ => ψ)).symm
  rw [h, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul] at hi
  have hc : haarScalarFactor ν ν₀ = 1 := by
    have he := mul_right_cancel₀ htest (hi.trans (one_mul _).symm)
    exact_mod_cast he
  rw [h, hc, one_smul]

theorem splitGLCoordinates_measurePreserving (μ : Measure G) [μ.IsHaarMeasure] (ν : Measure GE)
    [ν.IsHaarMeasure] (hν : IsSplitProductHaar μ ν) :
    MeasurePreserving κ ν (Measure.pi (fun _ : Fin m => μ)) := by
  let := LocalFieldTopology.generalLinear_secondCountableTopology F n
  refine ⟨(κ).continuous.measurable, ?_⟩
  rw [eq_splitProductMeasure μ ν hν, splitProductMeasure]
  exact MeasurableEquiv.map_map_symm (κ).toHomeomorph.toMeasurableEquiv

end Measures

end Langlands.BaseChange
