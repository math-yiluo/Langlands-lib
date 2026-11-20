import Langlands.Analysis.LocalSobolevPointwise
import Langlands.Analysis.UnitGroupLocalHaarComparison
import Langlands.Automorphic.CuspidalL2.Representation
import Langlands.Automorphic.OperatorBandLocalMeasure
import Langlands.Automorphic.OperatorRealizationCountable
import Langlands.Global.AdelicGLTopology
import Langlands.Global.HeckeDeterminantLocalConstancy
import Langlands.Topology.CompactOpen.NeighborhoodBasis

/-! # Product patches for the actual band Sobolev estimate -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 80000

open scoped Classical ContDiff ENNReal NNReal Matrix.Norms.Operator
open MeasureTheory MeasureTheory.Measure Set Metric Filter Topology

namespace Langlands.Automorphic.OperatorDeterminantSlice

open Langlands.Global ArchimedeanGL ContinuousRationalFunctions

universe u

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

/-- The full adelic splitting with its infinite component in the matrix
unit chart. -/
def matrixSplit : AdelicGL F n ≃ₜ* ArchimedeanGL F n × FiniteAdelicGL F n :=
  (AdelicGL.split F n).trans <|
    ContinuousMulEquiv.mk'
      ((archimedeanGLCoordinates F n).toHomeomorph.prodCongr (Homeomorph.refl _))
      (fun x y => Prod.ext (map_mul (archimedeanGLCoordinates F n) x.1 y.1) rfl)

theorem matrixSplit_apply (g : AdelicGL F n) :
    matrixSplit F n g =
      (archimedeanGLCoordinates F n (AdelicGL.infinite F n g), AdelicGL.finite F n g) := rfl

theorem matrixSplit_symm_apply (a : ArchimedeanGL F n) (b : FiniteAdelicGL F n) :
    (matrixSplit F n).symm (a, b) =
      AdelicGL.pair F n ((archimedeanGLCoordinates F n).symm a) b := rfl

/-- The finite-coordinate coset obtained by right multiplication by the
level subgroup. -/
def finiteCoset (b : FiniteAdelicGL F n) (K : Subgroup (FiniteAdelicGL F n)) :
    Set (FiniteAdelicGL F n) := (fun k => b * k) '' (K : Set (FiniteAdelicGL F n))

/-- A patch consisting of an ambient matrix region and a finite right
level coset. -/
def matrixProductPatch (t : Set (ArchimedeanMatrix F n))
    (b : FiniteAdelicGL F n) (K : Subgroup (FiniteAdelicGL F n)) : Set (AdelicGL F n) :=
  (matrixSplit F n) ⁻¹' ((Units.val ⁻¹' t) ×ˢ finiteCoset F n b K)

/-- At a band point choose an injective compact product patch with a
closed matrix ball and a translate of a compact open subgroup of `J`. -/
theorem exists_closedBall_productPatch (g : AdelicGL F n) (hg : point F n g ∈ band F n)
    (J : Subgroup (FiniteAdelicGL F n)) (hJ : IsOpen (J : Set (FiniteAdelicGL F n))) :
    ∃ (ρ : ℝ) (K : OpenSubgroup (FiniteAdelicGL F n)), 0 < ρ ∧
      IsCompact (K : Set (FiniteAdelicGL F n)) ∧ K.toSubgroup ≤ J ∧
      (closedBall ((matrixSplit F n g).1 : ArchimedeanMatrix F n) ρ) ⊆
        range (Units.val : ArchimedeanGL F n → ArchimedeanMatrix F n) ∧
      let P := matrixProductPatch F n
        (closedBall ((matrixSplit F n g).1 : ArchimedeanMatrix F n) ρ)
        (matrixSplit F n g).2 K.toSubgroup
      P.InjOn (point F n) ∧ MapsTo (point F n) P (band F n) := by
  let : NonarchimedeanGroup (FiniteAdelicGL F n) := finiteAdelicGL_nonarchimedeanGroup F n
  let e := matrixSplit F n
  let a := (e g).1
  let b := (e g).2
  obtain ⟨P, hPo, hgP, hPi, hPb⟩ := exists_open_injective_bandPatch F n g hg
  have hU : IsOpen (e.symm ⁻¹' P) := hPo.preimage e.symm.continuous
  have hab : (a, b) ∈ e.symm ⁻¹' P := by
    change e.symm (e g) ∈ P
    rwa [e.symm_apply_apply]
  obtain ⟨A, B, hAo, hBo, haA, hbB, hAB⟩ := isOpen_prod_iff.mp hU a b hab
  let U : Set (ArchimedeanMatrix F n) := Units.val '' A
  have hUo : IsOpen U := Units.isOpenMap_val _ hAo
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hUo (↑a : ArchimedeanMatrix F n) ⟨a, haA, rfl⟩
  let ρ := r / 2
  have hρ : 0 < ρ := half_pos hr
  have hρU : closedBall (↑a : ArchimedeanMatrix F n) ρ ⊆ U :=
    (closedBall_subset_ball (half_lt_self hr)).trans hrU
  let V : Set (FiniteAdelicGL F n) := (fun k => b * k) ⁻¹' B ∩ (J : Set (FiniteAdelicGL F n))
  have hV : V ∈ 𝓝 (1 : FiniteAdelicGL F n) :=
    ((hBo.preimage (continuous_const_mul b)).inter hJ).mem_nhds
      ⟨by simpa using hbB, J.one_mem⟩
  obtain ⟨K, hKc, hKV⟩ := Langlands.compactOpenSubgroupBasis (FiniteAdelicGL F n) V hV
  refine ⟨ρ, K, hρ, hKc, fun k hk => (hKV hk).2,
    hρU.trans (image_subset_range _ _), ?_⟩
  have hsub : matrixProductPatch F n (closedBall (↑a : ArchimedeanMatrix F n) ρ) b
      K.toSubgroup ⊆ P := by
    intro x hx
    change (↑(e x).1 : ArchimedeanMatrix F n) ∈ closedBall (↑a : ArchimedeanMatrix F n) ρ ∧
      (e x).2 ∈ finiteCoset F n b K.toSubgroup at hx
    have hxa : (e x).1 ∈ A := by
      obtain ⟨y, hy, he⟩ := hρU hx.1
      exact Units.val_injective he ▸ hy
    have hxb : (e x).2 ∈ B := by
      obtain ⟨k, hk, he⟩ := hx.2
      exact he ▸ (hKV hk).1
    have h := hAB (show e x ∈ A ×ˢ B from ⟨hxa, hxb⟩)
    change e.symm (e x) ∈ P at h
    rwa [e.symm_apply_apply] at h
  exact ⟨hPi.mono hsub, fun _ hx => hPb (hsub hx)⟩

local instance productRationalGroup : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance productContinuousGroup : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance productFiniteSmoothGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance productFormsGroup : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance productStableGroup : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _

variable (S : OperatorRealization F n)
local instance productSpaceGroup : AddCommGroup S.Space := Submodule.addCommGroup _

/-- The smooth original vector on a fixed finite slice expressed in the
ambient matrix coordinates. -/
def coordinateSlice (b : FiniteAdelicGL F n) (v : S.Space) :
    ArchimedeanMatrix F n → ℂ :=
  coordinateExtension F n (finiteSmoothSlice F n b (S.ambient v))

@[simp]
theorem coordinateSlice_apply_unit (b : FiniteAdelicGL F n) (v : S.Space)
    (a : ArchimedeanGL F n) :
    coordinateSlice F n S b v (a : ArchimedeanMatrix F n) =
      evaluate F n (S.toContinuous v) ((matrixSplit F n).symm (a, b)) := by
  rw [coordinateSlice, coordinateExtension_apply, finiteSmoothSlice_apply, matrixSplit_symm_apply,
    S.evaluate_toContinuous]

/-- Right level invariance identifies every value on the finite coset
with the original slice at its center. -/
theorem evaluate_matrixSplit_symm_mul_right (a : ArchimedeanGL F n)
    (b k : FiniteAdelicGL F n) (v : S.Space) (hk : S.finiteRepresentation k v = v) :
    evaluate F n (S.toContinuous v) ((matrixSplit F n).symm (a, b * k)) =
      coordinateSlice F n S b v a := by
  let e := matrixSplit F n
  have hk' : e (AdelicGL.ofFinite F n k) = (1, k) := by
    simp only [e, matrixSplit_apply, AdelicGL.infinite_ofFinite, AdelicGL.finite_ofFinite, map_one]
  have he : e.symm (a, b * k) = e.symm (a, b) * AdelicGL.ofFinite F n k := by
    apply e.injective
    simp only [map_mul, ContinuousMulEquiv.apply_symm_apply, hk', Prod.mk_mul_mk, mul_one]
  change evaluate F n (S.toContinuous v) (e.symm (a, b * k)) = _
  rw [he, ← S.evaluate_finiteRepresentation, hk, coordinateSlice_apply_unit]

variable [MeasurableSpace (AdelicGL F n)] [BorelSpace (AdelicGL F n)]
  [MeasurableSpace (ArchimedeanMatrix F n)] [BorelSpace (ArchimedeanMatrix F n)]

set_option maxHeartbeats 250000 in
/-- The additive integral of the original vector on a compact coordinate
slice is bounded by its band quotient `L²` norm, uniformly on vectors
fixed by the chosen finite level. -/
theorem exists_lintegral_coordinateSlice_le (μ : Measure (ArchimedeanMatrix F n))
    [IsAddHaarMeasure μ]
    (hL2 : ∀ v : S.Space,
      MemLp (toQuotient F n S v) 2 ((quotientHaarMeasure F n).restrict (band F n)))
    (t : Set (ArchimedeanMatrix F n)) (ht : IsCompact t)
    (htu : t ⊆ range (Units.val : ArchimedeanGL F n → ArchimedeanMatrix F n))
    (b : FiniteAdelicGL F n) (K : OpenSubgroup (FiniteAdelicGL F n))
    (hKc : IsCompact (K : Set (FiniteAdelicGL F n)))
    (hinj : (matrixProductPatch F n t b K.toSubgroup).InjOn (point F n))
    (hband : MapsTo (point F n) (matrixProductPatch F n t b K.toSubgroup) (band F n)) :
    ∃ C : ℝ≥0, ∀ v : S.Space,
      (∀ k : K, S.finiteRepresentation (k : FiniteAdelicGL F n) v = v) →
      ∫⁻ x in t, ‖coordinateSlice F n S b v x‖ₑ ∂μ ≤
        C * ‖toL2 F n S (quotientHaarMeasure F n) hL2 v‖ₑ := by
  let : SecondCountableTopology (FiniteAdelicGL F n) := finiteAdelicGL_secondCountableTopology F n
  let : CompleteSpace (ArchimedeanMatrix F n) := FiniteDimensional.complete ℝ _
  let : BorelSpace (ArchimedeanGL F n) := Langlands.Analysis.UnitGroupHaar.borelSpace_units
  borelize (FiniteAdelicGL F n)
  let e := matrixSplit F n
  let s := finiteCoset F n b K.toSubgroup
  have hso : IsOpen s := isOpenMap_mul_left b _ K.isOpen
  have hsc : IsCompact s := hKc.image (continuous_const_mul b)
  have hsn : s.Nonempty := ⟨b * 1, ⟨1, K.one_mem, rfl⟩⟩
  let η := matrixHaarMeasure F n
  have hη : IsHaarMeasure η := matrixHaarMeasure_isHaarMeasure F n
  obtain ⟨C, hC⟩ := Langlands.Analysis.UnitGroupHaar.exists_lintegral_productPatch_le
    μ η e t ht htu s hso hsc hsn
  let P := matrixProductPatch F n t b K.toSubgroup
  have hPc : IsCompact P := by
    apply e.toHomeomorph.isCompact_preimage.mpr
    refine IsCompact.prod ?_ hsc
    exact Units.isOpenEmbedding_val.isEmbedding.isCompact_iff.mpr
      (by rwa [image_preimage_eq_of_subset htu])
  have hPm : MeasurableSet P := by
    exact ((ht.measurableSet.preimage Units.continuous_val.measurable).prod hso.measurableSet).preimage
      e.continuous.measurable
  let M : ℝ≥0∞ := η P ^ (1 / 2 : ℝ)
  have hMt : M ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hPc.measure_lt_top.ne
  refine ⟨C * M.toNNReal, ?_⟩
  intro v hv
  let f := evaluate F n (S.toContinuous v)
  let p := coordinateSlice F n S b v
  have hf : Continuous f := continuous_evaluate F n (S.toContinuous v)
  have heq : ∀ a : ArchimedeanGL F n, (a : ArchimedeanMatrix F n) ∈ t →
      ∀ y ∈ s, ‖f (e.symm (a, y))‖ₑ = ‖p a‖ₑ := by
    intro a _ y hy
    obtain ⟨k, hk, rfl⟩ := hy
    exact congrArg (fun z : ℂ => ‖z‖ₑ)
      (evaluate_matrixSplit_symm_mul_right F n S a b k v (hv ⟨k, hk⟩))
  rw [ENNReal.coe_mul, ENNReal.coe_toNNReal hMt, mul_assoc]
  calc
    ∫⁻ x in t, ‖p x‖ₑ ∂μ ≤ (C : ℝ≥0∞) * ∫⁻ g in P, ‖f g‖ₑ ∂η :=
      hC _ _ hf.measurable.enorm heq
    _ ≤ (C : ℝ≥0∞) * (M * eLpNorm f 2 (η.restrict P)) :=
      mul_le_mul' le_rfl
        (Langlands.Analysis.setLIntegral_enorm_le_measure_rpow_mul_eLpNorm η hf.aestronglyMeasurable)
    _ ≤ _ := mul_le_mul' le_rfl (mul_le_mul' le_rfl
      (eLpNorm_bandPatch_le F n S hL2 P hPm hinj hband v))

end Langlands.Automorphic.OperatorDeterminantSlice
