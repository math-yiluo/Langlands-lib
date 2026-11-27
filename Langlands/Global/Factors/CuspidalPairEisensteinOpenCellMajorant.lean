import Langlands.Global.Factors.CuspidalPairEisensteinOpenCellLocalSum
import Langlands.Global.RankinSelberg.EqualAnalyticProduct
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-! # A product majorant on `M_((t+1)×(r+1))(𝔸)` with finite integral

The function
`Ω_β(Y) = (1 + ‖Y_∞‖)^(-β) · ∏_(v finite) max(1, ‖Y_v‖)^(-β)`
on adelic `(t + 1) × (r + 1)` matrices, where `‖Y_∞‖` is the norm of the archimedean
coordinates of the entries and `‖Y_v‖` the maximum norm of the entries at `v`, has finite
lower integral for every additive Haar measure once `β` exceeds both the real dimension of the
archimedean coordinates and `(t + 1)(r + 1) + 1`. See the paired Markdown. -/

noncomputable section

set_option autoImplicit false

universe u

open NumberField IsDedekindDomain MeasureTheory
open scoped NNReal ENNReal Classical

namespace Langlands.Global.CuspidalPairEisenstein.OpenCellMajorant

open OpenCellExhaustion RankinSelbergGlobal

variable {F : Type u} [Field F] [NumberField F]

section Flatten

variable (F) (a b : ℕ)

/-- The entries of an adelic `a × b` matrix as an adelic row vector of length `a b`. -/
def flatten : Matrix (Fin a) (Fin b) (Adeles F) ≃ₜ+ RowVector F (a * b) where
  toFun Y := Matrix.of fun _ q => Y (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2
  invFun x := Matrix.of fun i j => x 0 (finProdFinEquiv (i, j))
  left_inv Y := by
    ext i j
    change Y (finProdFinEquiv.symm (finProdFinEquiv (i, j))).1
      (finProdFinEquiv.symm (finProdFinEquiv (i, j))).2 = Y i j
    rw [Equiv.symm_apply_apply]
  right_inv x := by
    ext i q
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    change x 0 (finProdFinEquiv ((finProdFinEquiv.symm q).1, (finProdFinEquiv.symm q).2)) = x 0 q
    rw [Prod.mk.eta, Equiv.apply_symm_apply]
  map_add' _ _ := rfl
  continuous_toFun := continuous_matrix fun _ q =>
    continuous_id.matrix_elem (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2
  continuous_invFun := continuous_matrix fun i j =>
    continuous_id.matrix_elem 0 (finProdFinEquiv (i, j))

end Flatten

theorem norm_le_one_iff_mem_integers {v : FinitePlace F} (x : FiniteCompletion F v) :
    ‖x‖ ≤ 1 ↔ x ∈ v.adicCompletionIntegers F := by
  rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
  exact Valued.toNormedField.norm_le_one_iff

variable {r t : ℕ}

/-- The archimedean weight `(1 + ‖Y_∞‖)^(-β)`. -/
def archWeight (β : ℝ) (Y : Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F)) : ℝ :=
  (1 + ‖archimedeanCoordinates F ((t + 1) * (r + 1)) (flatten F (t + 1) (r + 1) Y)‖) ^ (-β)

/-- The local weight `max(1, ‖Y_v‖)^(-β)` at a finite place `v`. -/
def localWeight (β : ℝ) (v : FinitePlace F) (Y : Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F)) :
    ℝ :=
  (max 1 (entryNorm (matrixComponent v Y))) ^ (-β)

/-- The finite weight `∏_(v finite) max(1, ‖Y_v‖)^(-β)`; almost all factors are `1`. -/
def finiteWeight (β : ℝ) (Y : Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F)) : ℝ :=
  ∏ᶠ v, localWeight β v Y

/-- The majorant `Ω_β(Y) = (1 + ‖Y_∞‖)^(-β) ∏_v max(1, ‖Y_v‖)^(-β)`. -/
def majorant (β : ℝ) (Y : Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F)) : ℝ :=
  archWeight β Y * finiteWeight β Y

theorem localWeight_pos (β : ℝ) (v : FinitePlace F)
    (Y : Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F)) : 0 < localWeight β v Y :=
  Real.rpow_pos_of_pos (zero_lt_one.trans_le (le_max_left _ _)) _

theorem archWeight_pos (β : ℝ) (Y : Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F)) :
    0 < archWeight β Y :=
  Real.rpow_pos_of_pos (by positivity) _

theorem entryNorm_matrixComponent_le_one {v : FinitePlace F}
    {Y : Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F)}
    (hY : ∀ i j, matrixComponent v Y i j ∈ v.adicCompletionIntegers F) :
    entryNorm (matrixComponent v Y) ≤ 1 :=
  (entryNorm_le_iff zero_le_one).2 fun i j => (norm_le_one_iff_mem_integers _).2 (hY i j)

theorem localWeight_eq_one {β : ℝ} {v : FinitePlace F}
    {Y : Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F)}
    (hY : ∀ i j, matrixComponent v Y i j ∈ v.adicCompletionIntegers F) :
    localWeight β v Y = 1 := by
  rw [localWeight, max_eq_left (entryNorm_matrixComponent_le_one hY), Real.one_rpow]

theorem mulSupport_localWeight_finite (β : ℝ)
    (Y : Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F)) :
    (Function.mulSupport fun v => localWeight β v Y).Finite := by
  obtain ⟨A, hA⟩ := exists_mem_integralOutside (r := r) (t := t) Y
  refine A.finite_toSet.subset fun v hv => ?_
  by_contra hvA
  exact hv (localWeight_eq_one (hA v hvA))

theorem finiteWeight_pos (β : ℝ) (Y : Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F)) :
    0 < finiteWeight β Y :=
  finprod_induction (fun x => 0 < x) one_pos (fun _ _ => mul_pos) fun v => localWeight_pos β v Y

theorem majorant_pos (β : ℝ) (Y : Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F)) :
    0 < majorant β Y :=
  mul_pos (archWeight_pos β Y) (finiteWeight_pos β Y)

theorem finiteWeight_eq_one_of_mem {β : ℝ} {Y : Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F)}
    (hY : Y ∈ integralOutside F r t ∅) : finiteWeight β Y = 1 := by
  rw [finiteWeight]
  exact finprod_eq_one_of_forall_eq_one fun v => localWeight_eq_one (hY v (Finset.notMem_empty v))

section Translate

variable {A : Finset (FinitePlace F)} {v : FinitePlace F}

theorem archWeight_localMatrix_add (β : ℝ) (y : Matrix (Fin (t + 1)) (Fin (r + 1)) (FiniteCompletion F v))
    (Z : Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F)) :
    archWeight β (localMatrix v y + Z) = archWeight β Z := by
  have h : archimedeanCoordinates F ((t + 1) * (r + 1))
      (flatten F (t + 1) (r + 1) (localMatrix v y + Z)) =
      archimedeanCoordinates F ((t + 1) * (r + 1)) (flatten F (t + 1) (r + 1) Z) := by
    funext q
    change InfiniteAdeleRing.ringEquiv_mixedSpace F ((localMatrix v y + Z) _ _).1 =
      InfiniteAdeleRing.ringEquiv_mixedSpace F (Z _ _).1
    congr 1
    change (localAdele v (y _ _)).1 + (Z _ _).1 = (Z _ _).1
    change (0 : InfiniteAdeles F) + _ = _
    rw [zero_add]
  rw [archWeight, archWeight, h]

theorem localWeight_localMatrix_add (β : ℝ) (y : LocalQuotient r t v)
    {Z : Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F)} (hZ : ∀ i j,
      matrixComponent v Z i j ∈ v.adicCompletionIntegers F) (w : FinitePlace F) :
    localWeight β w (localMatrix v (Quotient.out y) + Z) =
      if w = v then classHeight v y ^ (-β) else localWeight β w Z := by
  split_ifs with hw
  · subst hw
    rw [localWeight, matrixComponent_add, matrixComponent_localMatrix,
      max_one_entryNorm_add _ _ (entryNorm_matrixComponent_le_one hZ)]
    rfl
  · rw [localWeight, localWeight, matrixComponent_add, matrixComponent_localMatrix_of_ne hw,
      zero_add]

theorem finiteWeight_localMatrix_add (β : ℝ) (y : LocalQuotient r t v)
    {Z : Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F)} (hZ : ∀ i j,
      matrixComponent v Z i j ∈ v.adicCompletionIntegers F) :
    finiteWeight β (localMatrix v (Quotient.out y) + Z) =
      classHeight v y ^ (-β) * finiteWeight β Z := by
  rw [finiteWeight, finiteWeight,
    ← mul_finprod_cond_ne v (mulSupport_localWeight_finite β (localMatrix v (Quotient.out y) + Z)),
    ← mul_finprod_cond_ne v (mulSupport_localWeight_finite β Z),
    localWeight_localMatrix_add β y hZ, ite_eq_left rfl, localWeight_eq_one hZ, one_mul]
  congr 1
  refine finprod_congr fun w => finprod_congr fun hw => ?_
  rw [localWeight_localMatrix_add β y hZ, ite_eq_right hw]

theorem majorant_localMatrix_add (β : ℝ) (y : LocalQuotient r t v)
    {Z : Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F)} (hZ : ∀ i j,
      matrixComponent v Z i j ∈ v.adicCompletionIntegers F) :
    majorant β (localMatrix v (Quotient.out y) + Z) =
      classHeight v y ^ (-β) * majorant β Z := by
  rw [majorant, majorant, archWeight_localMatrix_add, finiteWeight_localMatrix_add β y hZ]
  ring

end Translate

section Measure

local instance matrixMeasurableSpace :
    MeasurableSpace (Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F)) := borel _
local instance matrixBorelSpace :
    BorelSpace (Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F)) := ⟨rfl⟩

variable (μ : Measure (Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F)))

/-- The local factor `c_v = ∑_(y ∈ M(F_v)/M(𝒪_v)) max(1, ‖y‖)^(-β)`. -/
def localFactor (r t : ℕ) (β : ℝ) (v : FinitePlace F) : ℝ≥0∞ :=
  ∑' y : LocalQuotient r t v, ENNReal.ofReal (classHeight v y ^ (-β))

/-- **One-place step** for the majorant: for a left invariant measure and `v ∉ A`,
`∫_(U_(A ∪ {v})) Ω_β = c_v · ∫_(U_A) Ω_β` (lower integrals). -/
theorem setLIntegral_cons [μ.IsAddLeftInvariant] (β : ℝ) (A : Finset (FinitePlace F))
    (v : FinitePlace F) (hv : v ∉ A) :
    ∫⁻ Y in integralOutside F r t (Finset.cons v A hv), ENNReal.ofReal (majorant β Y) ∂μ =
      localFactor r t β v * ∫⁻ Y in integralOutside F r t A, ENNReal.ofReal (majorant β Y) ∂μ := by
  rw [← iUnion_cell r t A v hv, lintegral_iUnion (measurableSet_cell A v)
    (pairwise_disjoint_cell r t A v hv), localFactor, ← ENNReal.tsum_mul_right]
  refine tsum_congr fun y => ?_
  rw [cell, ← (measurePreserving_add_left μ _).setLIntegral_comp_emb
    (measurableEmbedding_addLeft _), ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_congr_fun (measurableSet_integralOutside A) fun Z hZ => ?_
  rw [majorant_localMatrix_add β y (hZ v hv),
    ENNReal.ofReal_mul (Real.rpow_nonneg (zero_le_one.trans (one_le_classHeight y)) _)]

theorem setLIntegral_eq_prod [μ.IsAddLeftInvariant] (β : ℝ) (A : Finset (FinitePlace F)) :
    ∫⁻ Y in integralOutside F r t A, ENNReal.ofReal (majorant β Y) ∂μ =
      (∏ v ∈ A, localFactor r t β v) *
        ∫⁻ Y in integralOutside F r t ∅, ENNReal.ofReal (majorant β Y) ∂μ := by
  classical
  induction A using Finset.induction_on with
  | empty => rw [Finset.prod_empty, one_mul]
  | insert v A hv ih =>
    rw [← Finset.cons_eq_insert v A hv, setLIntegral_cons μ β A v hv, ih,
      Finset.prod_cons, mul_assoc]

theorem lintegral_eq_iSup (β : ℝ) :
    ∫⁻ Y, ENNReal.ofReal (majorant β Y) ∂μ =
      ⨆ A : Finset (FinitePlace F),
        ∫⁻ Y in integralOutside F r t A, ENNReal.ofReal (majorant β Y) ∂μ := by
  have : Countable (FinitePlace F) := finitePlace_countable F
  set ν := μ.withDensity fun Y => ENNReal.ofReal (majorant β Y)
  have hU : (⋃ A : Finset (FinitePlace F), integralOutside F r t A) = Set.univ := by
    refine Set.eq_univ_of_forall fun Y => ?_
    obtain ⟨A, hA⟩ := exists_mem_integralOutside (r := r) (t := t) Y
    exact Set.mem_iUnion.mpr ⟨A, hA⟩
  have hd : Directed (· ⊆ ·) fun A : Finset (FinitePlace F) => integralOutside F r t A := by
    classical
    intro A B
    exact ⟨A ∪ B, integralOutside_mono r t Finset.subset_union_left,
      integralOutside_mono r t Finset.subset_union_right⟩
  have h := hd.measure_iUnion (μ := ν)
  rw [hU, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h
  rw [h]
  exact iSup_congr fun A => withDensity_apply _ (measurableSet_integralOutside A)

end Measure

section Base

local instance finiteAdelesMeasurableSpace : MeasurableSpace (FiniteAdeles F) := borel _
local instance finiteAdelesBorelSpace : BorelSpace (FiniteAdeles F) := ⟨rfl⟩
local instance finiteAdelesSecondCountable : SecondCountableTopology (FiniteAdeles F) :=
  finiteAdeles_secondCountableTopology F
local instance finiteAdelesLocallyCompact : LocallyCompactSpace (FiniteAdeles F) :=
  finiteAdeles_locallyCompactSpace F
local instance adelesSecondCountable : SecondCountableTopology (Adeles F) :=
  adeles_secondCountableTopology F
local instance adelesLocallyCompact : LocallyCompactSpace (Adeles F) :=
  adeles_locallyCompactSpace F
local instance finiteAdelesT2 : T2Space (FiniteAdeles F) := EqualAnalytic.t2Space_finiteAdeles F
local instance matrixMeasurableSpace' :
    MeasurableSpace (Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F)) := borel _
local instance matrixBorelSpace' :
    BorelSpace (Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F)) := ⟨rfl⟩

variable (F) in
/-- The splitting of an adelic `a × b` matrix into the archimedean and the finite-adelic
coordinates of its entries. -/
def matrixSplit (a b : ℕ) :
    Matrix (Fin a) (Fin b) (Adeles F) ≃ₜ+
      EqualAnalytic.ArchRow F (a * b) × EqualAnalytic.FinRow F (a * b) :=
  (flatten F a b).trans (EqualAnalytic.rowSplit F (a * b))

variable (F) in
/-- Finite-adelic row vectors with integral entries. -/
def integralRows (n : ℕ) : Set (EqualAnalytic.FinRow F n) :=
  Set.univ.pi fun _ => (integralFiniteAdeles F : Set (FiniteAdeles F))

theorem isCompact_integralRows (n : ℕ) : IsCompact (integralRows F n) :=
  isCompact_univ_pi fun _ => isCompact_integralFiniteAdeles F

theorem matrixSplit_snd_mem {Y : Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F)}
    (hY : Y ∈ integralOutside F r t ∅) :
    (matrixSplit F (t + 1) (r + 1) Y).2 ∈ integralRows F ((t + 1) * (r + 1)) := by
  intro q _
  rw [SetLike.mem_coe, mem_integralFiniteAdeles]
  intro v
  exact hY v (Finset.notMem_empty v) _ _

theorem archWeight_eq (β : ℝ) (Y : Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F)) :
    archWeight β Y = (1 + ‖(matrixSplit F (t + 1) (r + 1) Y).1‖) ^ (-β) :=
  rfl

/-- **Base case.** On `U_∅` the majorant is the archimedean weight times the indicator of
integral finite coordinates; its integral is finite once `β` exceeds the real dimension of
the archimedean coordinates. -/
theorem setLIntegral_empty_lt_top (μ : Measure (Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F)))
    [μ.IsAddHaarMeasure] {β : ℝ}
    (hβ : (Module.finrank ℝ (EqualAnalytic.ArchRow F ((t + 1) * (r + 1))) : ℝ) < β) :
    ∫⁻ Y in integralOutside F r t ∅, ENNReal.ofReal (majorant β Y) ∂μ < ⊤ := by
  have hK : IsCompact (integralRows F ((t + 1) * (r + 1))) := isCompact_integralRows _
  set g : EqualAnalytic.ArchRow F ((t + 1) * (r + 1)) ×
      EqualAnalytic.FinRow F ((t + 1) * (r + 1)) → ℝ≥0∞ := fun p =>
    ENNReal.ofReal ((1 + ‖p.1‖) ^ (-β)) *
      (integralRows F ((t + 1) * (r + 1))).indicator 1 p.2 with hg
  have hle : ∀ Y, (integralOutside F r t ∅).indicator
      (fun Y => ENNReal.ofReal (majorant β Y)) Y ≤ g (matrixSplit F (t + 1) (r + 1) Y) := by
    intro Y
    by_cases hY : Y ∈ integralOutside F r t ∅
    · rw [Set.indicator_of_mem hY, majorant, finiteWeight_eq_one_of_mem hY, mul_one,
        archWeight_eq]
      have h2 : (integralRows F ((t + 1) * (r + 1))).indicator
          (1 : EqualAnalytic.FinRow F ((t + 1) * (r + 1)) → ℝ≥0∞)
          (matrixSplit F (t + 1) (r + 1) Y).2 = 1 :=
        Set.indicator_of_mem (matrixSplit_snd_mem hY) _
      rw [hg]
      dsimp only
      rw [h2, mul_one]
    · rw [Set.indicator_of_notMem hY]
      exact zero_le
  set ρ : Measure (EqualAnalytic.ArchRow F ((t + 1) * (r + 1)) ×
      EqualAnalytic.FinRow F ((t + 1) * (r + 1))) :=
    (volume : Measure (EqualAnalytic.ArchRow F ((t + 1) * (r + 1)))).prod
      (Measure.addHaar : Measure (EqualAnalytic.FinRow F ((t + 1) * (r + 1))))
  set c := Measure.addHaarScalarFactor (Measure.map (matrixSplit F (t + 1) (r + 1)) μ) ρ
  have hρ : Measure.map (matrixSplit F (t + 1) (r + 1)) μ = c • ρ :=
    Measure.isAddLeftInvariant_eq_smul _ ρ
  have hmeas : Measurable fun x : EqualAnalytic.ArchRow F ((t + 1) * (r + 1)) =>
      ENNReal.ofReal ((1 + ‖x‖) ^ (-β)) := by fun_prop
  have hKm : Measurable ((integralRows F ((t + 1) * (r + 1))).indicator
      (1 : EqualAnalytic.FinRow F ((t + 1) * (r + 1)) → ℝ≥0∞)) :=
    measurable_one.indicator hK.measurableSet
  calc ∫⁻ Y in integralOutside F r t ∅, ENNReal.ofReal (majorant β Y) ∂μ
      = ∫⁻ Y, (integralOutside F r t ∅).indicator
          (fun Y => ENNReal.ofReal (majorant β Y)) Y ∂μ :=
        (lintegral_indicator (measurableSet_integralOutside ∅) _).symm
    _ ≤ ∫⁻ Y, g (matrixSplit F (t + 1) (r + 1) Y) ∂μ := lintegral_mono hle
    _ = ∫⁻ p, g p ∂(Measure.map (matrixSplit F (t + 1) (r + 1)) μ) :=
        ((matrixSplit F (t + 1) (r + 1)).toHomeomorph.measurableEmbedding.lintegral_map g).symm
    _ = ∫⁻ p, g p ∂(c • ρ) := congrArg (fun m => ∫⁻ p, g p ∂m) hρ
    _ = (c : ℝ≥0∞) * ∫⁻ p, g p ∂ρ := by
        rw [lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]
    _ = (c : ℝ≥0∞) * ((∫⁻ x, ENNReal.ofReal ((1 + ‖x‖) ^ (-β))) *
            ∫⁻ y, (integralRows F ((t + 1) * (r + 1))).indicator 1 y
              ∂(Measure.addHaar : Measure (EqualAnalytic.FinRow F ((t + 1) * (r + 1))))) := by
        rw [lintegral_prod_mul hmeas.aemeasurable hKm.aemeasurable]
    _ < ⊤ := by
        rw [lintegral_indicator_one hK.measurableSet]
        exact ENNReal.mul_lt_top ENNReal.coe_lt_top
          (ENNReal.mul_lt_top (finite_integral_one_add_norm hβ) hK.measure_lt_top)


theorem two_le_absNorm (v : FinitePlace F) : (2 : ℝ) ≤ Ideal.absNorm v.asIdeal := by
  have h := NumberField.HeightOneSpectrum.one_lt_absNorm v
  exact_mod_cast h

/-- For `β > D + 1`, `D = (t + 1)(r + 1)`, the local factors are bounded by
`1 + 2 N(v)^(D - β)`. -/
theorem localFactor_le {β : ℝ} (hβ : (((t + 1) * (r + 1) : ℕ) : ℝ) + 1 < β)
    (v : FinitePlace F) :
    localFactor r t β v ≤
      ENNReal.ofReal (1 + 2 * (Ideal.absNorm v.asIdeal : ℝ) ^ (((t + 1) * (r + 1) : ℕ) - β)) := by
  have hq := two_le_absNorm v
  have hβ0 : 0 ≤ β := by
    have : (0 : ℝ) ≤ (((t + 1) * (r + 1) : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  refine tsum_classHeight_rpow_le (v := v) hβ0 ?_
  calc (Ideal.absNorm v.asIdeal : ℝ) ^ ((((t + 1) * (r + 1) : ℕ) : ℝ) - β)
      ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    _ = (Ideal.absNorm v.asIdeal : ℝ)⁻¹ := Real.rpow_neg_one _
    _ ≤ 1 / 2 := by
        rw [one_div]
        exact inv_anti₀ two_pos hq

/-- For `β > D + 1`, `D = (t + 1)(r + 1)`, the series `∑_v N(v)^(D - β)` converges. -/
theorem summable_localExponent {β : ℝ} (hβ : (((t + 1) * (r + 1) : ℕ) : ℝ) + 1 < β) :
    Summable fun v : FinitePlace F =>
      (Ideal.absNorm v.asIdeal : ℝ) ^ ((((t + 1) * (r + 1) : ℕ) : ℝ) - β) := by
  have h := HeckeEulerProduct.summable_absNorm_rpow (K := F)
    (σ := β - (((t + 1) * (r + 1) : ℕ) : ℝ)) (by linarith)
  simpa only [neg_sub] using h

/-- For `β > D + 1`, `D = (t + 1)(r + 1)`, the finite products of local factors are bounded
uniformly by `exp(2 ∑_v N(v)^(D - β))`. -/
theorem prod_localFactor_le {β : ℝ} (hβ : (((t + 1) * (r + 1) : ℕ) : ℝ) + 1 < β)
    (A : Finset (FinitePlace F)) :
    ∏ v ∈ A, localFactor r t β v ≤
      ENNReal.ofReal (Real.exp (2 * ∑' v : FinitePlace F,
        (Ideal.absNorm v.asIdeal : ℝ) ^ ((((t + 1) * (r + 1) : ℕ) : ℝ) - β))) := by
  set x : FinitePlace F → ℝ := fun v =>
    (Ideal.absNorm v.asIdeal : ℝ) ^ ((((t + 1) * (r + 1) : ℕ) : ℝ) - β) with hx
  have hx0 : ∀ v, 0 ≤ x v := fun v => Real.rpow_nonneg (Nat.cast_nonneg _) _
  calc ∏ v ∈ A, localFactor r t β v ≤ ∏ v ∈ A, ENNReal.ofReal (1 + 2 * x v) :=
        Finset.prod_le_prod fun v _ => localFactor_le hβ v
    _ = ENNReal.ofReal (∏ v ∈ A, (1 + 2 * x v)) :=
        (ENNReal.ofReal_prod_of_nonneg fun v _ => by linarith [hx0 v]).symm
    _ ≤ ENNReal.ofReal (∏ v ∈ A, Real.exp (2 * x v)) := by
        refine ENNReal.ofReal_le_ofReal (Finset.prod_le_prod₀ (fun v _ => by linarith [hx0 v])
          fun v _ => ?_)
        have := Real.add_one_le_exp (2 * x v)
        linarith
    _ = ENNReal.ofReal (Real.exp (2 * ∑ v ∈ A, x v)) := by
        rw [Finset.mul_sum, Real.exp_sum]
    _ ≤ ENNReal.ofReal (Real.exp (2 * ∑' v, x v)) := by
        refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
        have := (summable_localExponent hβ).sum_le_tsum A fun v _ => hx0 v
        linarith

/-- **Finiteness of the majorant integral.** For every additive Haar measure on
`M_((t+1)×(r+1))(𝔸)`, `∫ Ω_β < ∞` once `β` exceeds both the real dimension of the
archimedean coordinates and `(t + 1)(r + 1) + 1`. -/
theorem lintegral_majorant_lt_top
    (μ : Measure (Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F))) [μ.IsAddHaarMeasure] {β : ℝ}
    (hβ₁ : (Module.finrank ℝ (EqualAnalytic.ArchRow F ((t + 1) * (r + 1))) : ℝ) < β)
    (hβ₂ : (((t + 1) * (r + 1) : ℕ) : ℝ) + 1 < β) :
    ∫⁻ Y, ENNReal.ofReal (majorant β Y) ∂μ < ⊤ := by
  rw [lintegral_eq_iSup]
  refine lt_of_le_of_lt (iSup_le fun A => ?_)
    (ENNReal.mul_lt_top (ENNReal.ofReal_lt_top (r := Real.exp (2 * ∑' v : FinitePlace F,
      (Ideal.absNorm v.asIdeal : ℝ) ^ ((((t + 1) * (r + 1) : ℕ) : ℝ) - β))))
      (setLIntegral_empty_lt_top μ hβ₁))
  rw [setLIntegral_eq_prod]
  exact mul_le_mul_left (prod_localFactor_le hβ₂ A) _

end Base

end Langlands.Global.CuspidalPairEisenstein.OpenCellMajorant
