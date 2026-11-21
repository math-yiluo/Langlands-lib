import Langlands.Automorphic.CuspidalLeviCoefficientSlices
import Langlands.Global.AdelicGLTopology
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Detection by cuspidal tests on compact subsets of the block Levi -/

noncomputable section
universe u
open NumberField MeasureTheory
open scoped Classical CategoryTheory.MonObj
set_option autoImplicit false
set_option quotPrecheck false

namespace Langlands.Automorphic

open Langlands.Global Langlands.GeneralLinear

private theorem eq_zero_of_forall_compact_integrals {X : Type*} [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X] (volumeMeasure : Measure X)
    [IsFiniteMeasureOnCompacts volumeMeasure] [Measure.IsOpenPosMeasure volumeMeasure] {f : X → ℂ} (hf : Continuous f)
    (h : ∀ K : Set X, IsCompact K → (∫ x in K, f x ∂volumeMeasure) = 0) : f = 0 := by
  funext x
  by_contra hx
  let c := star (f x)
  let g (y : X) : ℝ := (c * f y).re
  have hg : Continuous g := Complex.continuous_re.comp (continuous_const.mul hf)
  have hgx : 0 < g x := by
    change 0 < (star (f x) * f x).re
    rw [show star (f x) * f x = (Complex.normSq (f x) : ℂ) from Complex.normSq_eq_conj_mul_self.symm,
      Complex.ofReal_re]
    exact Complex.normSq_pos.mpr hx
  let a := g x / 2
  let U : Set X := {y | a < g y}
  have hU : IsOpen U := isOpen_lt continuous_const hg
  have hxU : x ∈ U := by dsimp [U, a]; linarith
  obtain ⟨K, hK, hxK, hKU⟩ := exists_compact_subset hU hxU
  have hKpos : 0 < volumeMeasure K := Measure.measure_pos_of_nonempty_interior volumeMeasure ⟨x, hxK⟩
  have hKreal : 0 < volumeMeasure.real K := ENNReal.toReal_pos hKpos.ne' hK.measure_ne_top
  have hfi : IntegrableOn (fun y => c * f y) K volumeMeasure :=
    (continuous_const.mul hf).continuousOn.integrableOn_compact hK
  have hzero : (∫ y in K, g y ∂volumeMeasure) = 0 := by
    have hi : (∫ y in K, c * f y ∂volumeMeasure) = 0 :=
      (integral_const_mul c f).trans ((congrArg (c * ·) (h K hK)).trans (mul_zero c))
    exact (integral_re hfi).trans ((congrArg Complex.re hi).trans Complex.zero_re)
  have hci : IntegrableOn (fun _ : X => a) K volumeMeasure := continuous_const.continuousOn.integrableOn_compact hK
  have hgi : IntegrableOn g K volumeMeasure := hg.continuousOn.integrableOn_compact hK
  have hl := setIntegral_mono_on hci hgi hK.measurableSet (fun y hy => (hKU hy : a < g y).le)
  rw [setIntegral_const, hzero, smul_eq_mul] at hl
  exact (not_le_of_gt (mul_pos hKreal (half_pos hgx))) hl

variable (F : Type u) [Field F] [NumberField F] {n : ℕ}

local instance leviTestRationalGroup (d : ℕ) : AddCommGroup (RationalInvariantFunctions F d) :=
  Submodule.addCommGroup _
local instance leviTestContinuousGroup (d : ℕ) : AddCommGroup (ContinuousRationalFunctions F d) :=
  Submodule.addCommGroup _
local instance leviTestSmoothGroup (d : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F d) :=
  Submodule.addCommGroup _
local instance leviTestFormsGroup (d : ℕ) : AddCommGroup (AutomorphicForms F d) := Submodule.addCommGroup _
local instance leviTestStableGroup (d : ℕ) : AddCommGroup (StableAutomorphicFunctions F d) := Submodule.addCommGroup _
local instance leviTestRealizationGroup {d : ℕ} (S : OperatorRealization F d) : AddCommGroup S.Space :=
  Submodule.addCommGroup _

local instance leviTestT2Space (B : BlockShape n) : T2Space (AdelicBlockParabolic.FullLevi F B) := by
  let : ∀ i : Fin B.length, T2Space (AdelicGL F (B.size i)) := fun i => adelicGL_t2Space F (B.size i)
  change T2Space (∀ i : Fin B.length, AdelicGL F (B.size i))
  infer_instance

local instance leviTestMeasurableSpace (B : BlockShape n) : MeasurableSpace (AdelicBlockParabolic.FullLevi F B) :=
  borel _
local instance leviTestBorelSpace (B : BlockShape n) : BorelSpace (AdelicBlockParabolic.FullLevi F B) :=
  ⟨rfl⟩

variable [CompactSpace (AdeleQuotient F)]

/-- Orthogonality on every compact test set to products of actual cuspidal block forms. -/
def OrthogonalToCuspidalLeviProducts (f : FiniteSmoothRationalFunctions F n) : Prop :=
  ∀ (B : BlockShape n) (g : AdelicGL F n)
    (v : ∀ i : Fin B.length, FiniteSmoothRationalFunctions F (B.size i)),
    (∀ i, IsAutomorphicForm F (B.size i) (finiteSmoothInclusion F (B.size i) (v i))) →
    (∀ i, IsCuspidal F (B.size i) (v i).val) →
    ∀ K : Set (AdelicBlockParabolic.FullLevi F B), IsCompact K →
      (∫ m in K, blockShapeLeviSlice F B f g m *
        star (∏ i, finiteSmoothFunctionEvaluation F (B.size i) (v i) (m i)) ∂Measure.haar) = 0

omit [CompactSpace (AdeleQuotient F)] in
set_option maxHeartbeats 450000 in
private theorem isAutomorphicForm_originalLeviSlice (S : OperatorRealization F n) (f : S.Space)
    (B : BlockShape n) (m : AdelicBlockParabolic.FullLevi F B) (i : Fin B.length) :
    IsAutomorphicForm F (B.size i) (finiteSmoothInclusion F (B.size i)
      (blockShapeLeviSliceFactorLinearMap F B i m (S.ambient f))) := by
  let d := B.size i
  let a := S.ambient f
  let v := blockShapeLeviSliceFactorLinearMap F B i m a
  have ha := S.isAutomorphicForm_ambient f
  refine ⟨(hasFiniteLevel_iff_mem_finiteSmooth F d v.val).mpr v.property.2, ?_, ?_, ?_⟩
  · have hp : AdelicGL.pair F n 1 1 = 1 := (AdelicGL.split F n).symm.map_one
    have h := blockShapeLeviSliceFactor_isInfiniteFinite_of_form B F (S.formInclusion f) 1 1 m i
    rw [Subgroup.coe_one, hp] at h
    exact h
  · exact blockShapeLeviSliceFactor_isCenterFinite F B i a ha.2.2.1 m
  · exact blockShapeLeviSliceFactor_hasPolynomialGrowth F B i a ha.2.2.2 1 m

omit [CompactSpace (AdeleQuotient F)] in
set_option maxHeartbeats 900000 in
private theorem exists_deepest_nonzero_blockTerm (f : FiniteSmoothRationalFunctions F n) (hf : f ≠ 0) :
    ∃ B : BlockShape n, (∃ g, blockShapeConstantTerm B F f g ≠ 0) ∧
      ∀ t : Finset (Fin (n - 1)), B.cuts ⊂ t →
        finiteSmoothBlockConstantTerm F (standardBlockWeight t) f = 0 := by
  let t₀ : Finset (Fin (n - 1)) := ∅
  let term := fun t : Finset (Fin (n - 1)) => finiteSmoothBlockConstantTerm F (standardBlockWeight t) f
  have hzero : term t₀ ≠ 0 := by
    intro h
    apply hf
    apply finiteSmoothFunctionEvaluation_injective F n
    funext g
    let e := GeneralLinearGroupPoints.adelicEquiv F n
    have h' := congrFun h (e.symm g)
    change finiteSmoothBlockConstantTerm F (standardBlockWeight ∅) f (e.symm g) = 0 at h'
    calc
      _ = finiteSmoothFunctionEvaluation F n f (e (e.symm g)) :=
        congrArg (finiteSmoothFunctionEvaluation F n f) (e.apply_symm_apply g).symm
      _ = finiteSmoothBlockConstantTerm F (standardBlockWeight ∅) f (e.symm g) :=
        (finiteSmoothBlockConstantTerm_empty F f (e.symm g)).symm
      _ = 0 := h'
      _ = _ := (congrFun ((finiteSmoothFunctionEvaluation F n).map_zero) g).symm
  let s := Finset.univ.filter (fun t => term t ≠ 0)
  have hs : s.Nonempty := ⟨t₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzero⟩⟩
  obtain ⟨t, ht, hmax⟩ := Finset.exists_max_image s Finset.card hs
  let B := (BlockShape.cutEquiv n).symm t
  have hB : B.cuts = t := BlockShape.cuts_cutEquiv_symm t
  have hnonzero : term t ≠ 0 := (Finset.mem_filter.mp ht).2
  obtain ⟨y, hy⟩ : ∃ y, term t y ≠ 0 := by
    by_contra! h
    exact hnonzero (funext h)
  let e := GeneralLinearGroupPoints.adelicEquiv F n
  refine ⟨B, ⟨e y, ?_⟩, fun t' ht' => ?_⟩
  · change finiteSmoothBlockConstantTerm F (standardBlockWeight B.cuts) f (e.symm (e y)) ≠ 0
    rw [hB, e.symm_apply_apply]
    exact hy
  · by_contra! h
    exact (not_le_of_gt (Finset.card_lt_card (hB ▸ ht')))
      (hmax t' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))

set_option maxHeartbeats 1100000 in
/-- Compact tests against products of actual cusp forms detect every realized automorphic form. -/
theorem eq_zero_of_orthogonalToCuspidalLeviProducts (S : OperatorRealization F n) (f : S.Space)
    (h : OrthogonalToCuspidalLeviProducts F (S.ambient f)) : f = 0 := by
  by_contra hn
  have hnf : S.ambient f ≠ 0 := fun hz => hn ((S.finiteSmoothAmbient_injective F) hz)
  obtain ⟨B, ⟨x, hx⟩, href⟩ := exists_deepest_nonzero_blockTerm F (S.ambient f) hnf
  obtain ⟨k, m, hm⟩ := blockShapeConstantTerm_eq_leviSlice_at_infiniteCompact F B (S.ambient f) x
  let d := AdelicGL.finite F n x
  let g := AdelicGL.pair F n k.val d
  let f' := S.compactRepresentation k (S.finiteRepresentation d f)
  have hf' : S.ambient f' = finiteSmoothRightAction F n g (S.ambient f) := by
    change finiteSmoothRightAction F n (AdelicGL.ofInfinite F n k.val)
      (finiteSmoothRightAction F n (AdelicGL.ofFinite F n d) (S.ambient f)) = _
    rw [← Module.End.mul_apply, ← map_mul, ← OperatorRealization.pair_eq_ofInfinite_mul_ofFinite]
  have hs (u : AdelicBlockParabolic.FullLevi F B) : blockShapeLeviSlice F B (S.ambient f') 1 u =
      blockShapeLeviSlice F B (S.ambient f) g u := by
    rw [hf', blockShapeLeviSlice_rightAction, one_mul]
  let v (i : Fin B.length) := blockShapeLeviSliceFactorLinearMap F B i m (S.ambient f')
  have heval (i : Fin B.length) (y : AdelicGL F (B.size i)) :
      finiteSmoothFunctionEvaluation F (B.size i) (v i) y =
      blockShapeLeviSlice F B (S.ambient f) g (Function.update m i y) := hs _
  have hvauto (i : Fin B.length) := isAutomorphicForm_originalLeviSlice F S f' B m i
  have hvcusp (i : Fin B.length) : IsCuspidal F (B.size i) (v i).val := by
    have he : (v i).val = blockShapeLeviSliceFactor B F (S.ambient f) g m i := by
      apply ContinuousRationalFunctions.toContinuousMap_injective F (B.size i)
      ext y
      exact heval i y
    exact he.symm ▸ isCuspidal_blockShapeLeviSliceFactor F B (S.ambient f) href g m i
  let ψ (u : AdelicBlockParabolic.FullLevi F B) :=
    ∏ i, finiteSmoothFunctionEvaluation F (B.size i) (v i) (u i)
  have hψ : Continuous ψ := continuous_finsetProd _ fun i _ =>
    (ContinuousRationalFunctions.continuous_evaluate F (B.size i) (v i).val).comp (continuous_apply i)
  let φ := blockShapeLeviSlice F B (S.ambient f) g
  have hφ : φ m ≠ 0 := fun hz => hx (hm.trans hz)
  have hψm : ψ m ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => by
    rw [heval i (m i), Function.update_eq_self]
    exact hφ
  let H := fun u => φ u * star (ψ u)
  have hH := (continuous_blockShapeLeviSlice F B (S.ambient f) g).mul (continuous_star.comp hψ)
  have he := eq_zero_of_forall_compact_integrals Measure.haar hH (h B g v hvauto hvcusp)
  exact (mul_ne_zero hφ (star_ne_zero.mpr hψm)) (congrFun he m)

end Langlands.Automorphic
