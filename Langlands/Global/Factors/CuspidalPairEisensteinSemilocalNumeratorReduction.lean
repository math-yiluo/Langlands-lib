import Langlands.Global.Factors.CuspidalPairEisensteinSemilocalNumeratorStatement
import Langlands.Global.Factors.CuspidalPairEisensteinOpenCellFiniteTranslation
import Langlands.Global.Factors.CuspidalPairEisensteinOpenCellArchimedeanMeasure

/-! # The semilocal numerator from the archimedean numerator

`CuspidalPairEisensteinSemilocalNumeratorStatement` follows from
`CuspidalPairEisensteinArchimedeanNumeratorStatement`: multiplying the archimedean section by
the indicator of the matrices whose open-cell coordinate lies in a small ball around `0` at
the places of `S₀` (a neighbourhood of the coset `P w` in the open chart `P w U'`) turns the
partial open-cell integral into a nonzero constant times the archimedean open-cell
integral. See the paired Markdown. -/

noncomputable section

set_option autoImplicit false

universe u

namespace Langlands.Global

open MeasureTheory NumberField CuspidalPairEisenstein
open Automorphic (CuspidalOperatorRealization)
open RankinSelbergGlobal (IsStandardAdditiveCharacter)
open Langlands.ClassFieldTheory.Global.RelativeWeilGroup (HasUnitaryCentralCharacter)

namespace CuspidalPairEisensteinSemilocalNumerator

open CuspidalPairEisenstein.OpenCellCutoff CuspidalPairEisenstein.Oneplace
  CuspidalPairEisenstein.OpenCellExhaustion CuspidalPairEisenstein.SemilocalCutoff
  CuspidalPairEisenstein.FiniteTranslation CuspidalPairEisenstein.ArchimedeanMeasure

variable {F : Type u} [Field F] [NumberField F] {r t : ℕ}

/-- The set `U_S` of matrices integral outside `S` is open. -/
theorem isOpen_integralOutside (S : Finset (FinitePlace F)) :
    IsOpen (integralOutside F r t S) := by
  have h : IsOpen {x : FiniteAdeles F | ∀ v, v ∉ S →
      x.1 v ∈ (v.adicCompletionIntegers F : Set (FiniteCompletion F v))} :=
    RestrictedProduct.isOpen_forall_imp_mem (fun v => Valued.isOpen_valuationSubring _)
  have e : integralOutside F r t S = ⋂ i, ⋂ j,
      (fun Y : Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F) => (Y i j).2) ⁻¹'
        {x : FiniteAdeles F | ∀ v, v ∉ S →
          x.1 v ∈ (v.adicCompletionIntegers F : Set (FiniteCompletion F v))} := by
    ext Y
    simp only [Set.mem_iInter, Set.mem_preimage]
    exact ⟨fun hY i j v hv => hY v hv i j, fun hY v hv i j => hY i j v hv⟩
  rw [e]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    h.preimage (continuous_snd.comp ((continuous_apply j).comp (continuous_apply i)))

variable (r t) in
/-- The matrices whose components at the places `v ∈ S₀` have entries of valuation
`< |ε_v|_v`. -/
def smallAt (S₀ : Finset (FinitePlace F)) (ε : ∀ v : FinitePlace F, FiniteCompletion F v) :
    Set (Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F)) :=
  {Y | ∀ v ∈ S₀, ∀ i j, Valued.v (matrixComponent v Y i j) < Valued.v (ε v)}

theorem isOpen_smallAt (S₀ : Finset (FinitePlace F))
    (ε : ∀ v : FinitePlace F, FiniteCompletion F v) : IsOpen (smallAt r t S₀ ε) := by
  have e : smallAt r t S₀ ε = ⋂ v ∈ S₀, ⋂ i, ⋂ j,
      (fun Y : Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F) => matrixComponent v Y i j) ⁻¹'
        {x : FiniteCompletion F v | Valued.v x < Valued.v (ε v)} := by
    ext Y
    simp only [smallAt, Set.mem_iInter, Set.mem_preimage]
    rfl
  rw [e]
  refine isOpen_biInter_finset fun v _ => isOpen_iInter_of_finite fun i =>
    isOpen_iInter_of_finite fun j => (isOpen_lt_valuation (ε v)).preimage ?_
  exact (RestrictedProduct.continuous_eval v).comp
    (continuous_snd.comp ((continuous_apply j).comp (continuous_apply i)))

theorem matrixComponent_archimedeanMatrix (v : FinitePlace F)
    (X : Matrix (Fin (t + 1)) (Fin (r + 1)) (InfiniteAdeles F)) :
    matrixComponent v (archimedeanMatrix F r t X) = 0 :=
  rfl

theorem matrixComponent_archimedeanMatrix_add (v : FinitePlace F)
    (X : Matrix (Fin (t + 1)) (Fin (r + 1)) (InfiniteAdeles F))
    (Y : Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F)) :
    matrixComponent v (archimedeanMatrix F r t X + Y) = matrixComponent v Y := by
  rw [matrixComponent_add, matrixComponent_archimedeanMatrix, zero_add]

end CuspidalPairEisensteinSemilocalNumerator

open CuspidalPairEisensteinSemilocalNumerator
open CuspidalPairEisenstein.OpenCellCutoff CuspidalPairEisenstein.Oneplace
  CuspidalPairEisenstein.OpenCellExhaustion CuspidalPairEisenstein.SemilocalCutoff
  CuspidalPairEisenstein.FiniteTranslation CuspidalPairEisenstein.ArchimedeanMeasure

/-- The archimedean numerator of the open-cell integral implies the semilocal numerator. -/
def CuspidalPairEisensteinSemilocalNumeratorReductionStatement : Prop :=
  CuspidalPairEisensteinArchimedeanNumeratorStatement.{u} →
    CuspidalPairEisensteinSemilocalNumeratorStatement.{u}

theorem cuspidalPairEisensteinSemilocalNumeratorReduction :
    CuspidalPairEisensteinSemilocalNumeratorReductionStatement.{u} := by
  classical
  intro hArch F _ _ _ r t T T' hT hT' ψ hψ S
  obtain ⟨S₁, hS₁⟩ := hArch F r t T T' hT hT' ψ hψ
  obtain ⟨Tψ, a, ha, hψbox⟩ := exists_finiteBox_eq_one ψ hψ.1
  refine ⟨S ∪ S₁ ∪ Tψ, Finset.subset_union_left.trans Finset.subset_union_left,
    fun s₀ hs₀ => ?_⟩
  set S₀ := S ∪ S₁ ∪ Tψ with hS₀
  have hS₁S₀ : S₁ ⊆ S₀ := Finset.subset_union_right.trans Finset.subset_union_left
  have hTψS₀ : Tψ ⊆ S₀ := Finset.subset_union_right
  obtain ⟨φ, hφ, hφsph, c, hcm, hca, hc0, σ, hσ⟩ := hS₁ s₀ hs₀
  obtain ⟨J, hJ⟩ := hφ.2.1
  choose b hb0 hb1 hbJ using fun v => exists_ball_openCellUnipotent_mem (r := r) (t := t) J v
  -- the thresholds `ε_v = b_v a_v`
  let ε : ∀ v : FinitePlace F, FiniteCompletion F v := fun v => b v * a v
  have hεb : ∀ v, Valued.v (ε v) ≤ Valued.v (b v) := fun v => by
    simp only [ε, map_mul]
    exact mul_le_of_le_one_right' (ha v).2
  have hεa : ∀ v, Valued.v (ε v) ≤ Valued.v (a v) := fun v => by
    simp only [ε, map_mul]
    exact mul_le_of_le_one_left' (hb1 v)
  have hε1 : ∀ v, Valued.v (ε v) ≤ 1 := fun v => (hεb v).trans (hb1 v)
  have hε0 : ∀ v, ε v ≠ 0 := fun v => mul_ne_zero (hb0 v) (ha v).1
  have hε : ∀ v ∈ S₀, ε v ≠ 0 ∧ Valued.v (ε v) ≤ 1 := fun v _ => ⟨hε0 v, hε1 v⟩
  -- the region `R = U_(S₀) ∩ {|Y_v| < |ε_v| for v ∈ S₀}`
  let C := smallAt r t S₀ ε
  let R := integralOutside F r t S₀ ∩ C
  have hCo : IsOpen C := isOpen_smallAt S₀ ε
  have hRo : IsOpen R := (isOpen_integralOutside S₀).inter hCo
  have hRint : ∀ Y ∈ R, ∀ v i j, matrixComponent v Y i j ∈ v.adicCompletionIntegers F := by
    intro Y hY v i j
    by_cases hv : v ∈ S₀
    · change Valued.v (matrixComponent v Y i j) ≤ 1
      exact (hY.2 v hv i j).le.trans (hε1 v)
    · exact hY.1 v hv i j
  have hR0 : (0 : Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F)) ∈ R := by
    refine ⟨fun v _ i j => (v.adicCompletionIntegers F).zero_mem, fun v _ i j => ?_⟩
    change Valued.v (0 : FiniteCompletion F v) < Valued.v (ε v)
    rw [map_zero]
    exact zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr (hε0 v))
  have hRadd : ∀ (X : Matrix (Fin (t + 1)) (Fin (r + 1)) (InfiniteAdeles F)) (Y), Y ∈ R →
      archimedeanMatrix F r t X + Y ∈ R := by
    intro X Y hY
    refine ⟨fun v hv i j => ?_, fun v hv i j => ?_⟩
    · change matrixComponent v (archimedeanMatrix F r t X + Y) i j ∈ _
      rw [matrixComponent_archimedeanMatrix_add]
      exact hY.1 v hv i j
    · change Valued.v (matrixComponent v (archimedeanMatrix F r t X + Y) i j) < _
      rw [matrixComponent_archimedeanMatrix_add]
      exact hY.2 v hv i j
  obtain ⟨κ, hκ, hκint⟩ := exists_setIntegral_comp_archimedeanPart hRo hR0 hRadd
    (fun Y hY i j => (mem_integralFiniteAdeles F _).mpr fun v => hRint Y hY v i j)
  have hm : MeromorphicOn (fun s => (κ : ℂ) * c s) Set.univ := fun x hx =>
    (MeromorphicAt.const (κ : ℂ) x).mul (hcm x hx)
  have han : AnalyticAt ℂ (fun s => (κ : ℂ) * c s) s₀ := analyticAt_const.mul hca
  have hκ' : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ
  refine ⟨fun g => cutoff r t S₀ ε g * φ g, isSection_cutoff_mul hε hφ,
    isSphericalSectionOutside_cutoff_mul hS₁S₀ hφsph, fun s => (κ : ℂ) * c s,
    hm, han, mul_ne_zero hκ' hc0, σ, fun s hs => ?_⟩
  obtain ⟨hInt, hcs⟩ := hσ s hs
  -- the integrand on the region
  have key : ∀ Y ∈ R, openCellIntegrand ψ φ s Y =
      archimedeanOpenCellIntegrand ψ φ s (archimedeanPart F r t Y) := by
    intro Y hY
    set Y₀ := archimedeanMatrix F r t (archimedeanPart F r t Y) with hY₀
    set Z := Y - Y₀ with hZ
    have hYZ : Y = Y₀ + Z := (add_sub_cancel Y₀ Y).symm
    have hZ1 : ∀ i j, (Z i j).1 = 0 := fun i j => by
      change (Y i j).1 - (Y i j).1 = 0
      exact sub_self _
    have hZc : ∀ v, matrixComponent v Z = matrixComponent v Y := fun v => by
      rw [hZ, matrixComponent_sub, hY₀, matrixComponent_archimedeanMatrix, sub_zero]
    have hZint : ∀ v i j, matrixComponent v Z i j ∈ v.adicCompletionIntegers F :=
      fun v i j => by
        rw [hZc]
        exact hRint Y hY v i j
    have hZS₁ : ∀ v ∈ S₁, FiniteAdelicGL.localInclusion F (r + t + 2) v
        (comp F (r + t + 2) v (openCellUnipotent F r t Z)) ∈ J := fun v hv => by
      rw [comp_openCellUnipotent]
      refine hbJ v _ fun i j => ?_
      rw [hZc]
      exact lt_of_lt_of_le (hY.2 v (hS₁S₀ hv) i j) (hεb v)
    have hψZ : ψ (Z (Fin.last t) 0) = 1 := by
      refine hψbox _ (hZ1 _ _) (fun v => hZint v _ _) (fun v hv => ?_)
      change Valued.v (matrixComponent v Z (Fin.last t) 0) < _
      rw [hZc]
      exact lt_of_lt_of_le (hY.2 v (hTψS₀ hv) _ _) (hεa v)
    have h := openCellIntegrand_add_of_invariant ψ φ s Y₀ Z
      (twisted_mul_openCellUnipotent J hJ hφsph.1 s hZ1 hZint hZS₁) hψZ
    rw [← hYZ] at h
    exact h
  -- the integrand of the cut-off section
  have hind : ∀ Y, openCellIntegrand ψ (fun g => cutoff r t S₀ ε g * φ g) s Y =
      C.indicator (openCellIntegrand ψ φ s) Y := by
    intro Y
    rw [openCellIntegrand_cutoff_mul, cutoff]
    by_cases hY : Y ∈ C
    · rw [Set.indicator_of_mem hY, ite_eq_left ((inCellAt_openCell_iff S₀ ε Y).mpr hY), one_mul]
    · rw [Set.indicator_of_notMem hY,
        ite_eq_right (fun h => hY ((inCellAt_openCell_iff S₀ ε Y).mp h)), zero_mul]
  let : MeasurableSpace (Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F)) := borel _
  let : MeasurableSpace (Matrix (Fin (t + 1)) (Fin (r + 1)) (InfiniteAdeles F)) := borel _
  have : BorelSpace (Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F)) := ⟨rfl⟩
  have hGm : AEStronglyMeasurable (archimedeanOpenCellIntegrand ψ φ s)
      (archimedeanOpenCellHaar F r t) := hInt.aestronglyMeasurable
  show (κ : ℂ) * c s = _
  rw [hcs]
  change (κ : ℂ) * ∫ X, archimedeanOpenCellIntegrand ψ φ s X ∂(archimedeanOpenCellHaar F r t) =
    ∫ Y in integralOutside F r t S₀,
      openCellIntegrand ψ (fun g => cutoff r t S₀ ε g * φ g) s Y ∂(openCellHaar F r t)
  rw [← hκint _ hGm]
  simp_rw [hind]
  rw [setIntegral_indicator hCo.measurableSet]
  exact (setIntegral_congr_fun hRo.measurableSet key).symm

end Langlands.Global
