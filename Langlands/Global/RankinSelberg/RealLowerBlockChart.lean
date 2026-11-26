import Langlands.Group.GL.RealBruhatTrailingChart
import Langlands.Group.GL.LowerTriangularBigCellConull
import Langlands.Group.GL.LowerBlockQuotientGeometryProof
import Langlands.Representation.RankinSelberg.LowerTriangularQuotientCellMeasure
import Langlands.Analysis.Local.QuotientNormalizingFunction
import Langlands.Global.RankinSelberg.ArchimedeanIntegrals
import Langlands.Global.RankinSelberg.RealIwasawaMeasure
import Langlands.Global.RankinSelberg.RealUnequalMellinReduction
import Langlands.Global.RankinSelberg.RealRankZeroHaar
import Mathlib.MeasureTheory.Group.Prod

/-! # The lower-block chart of real unipotent quotients

Over `ℝ`, the coset map of the invertible lower triangular matrices into `N_m \ GL_m(ℝ)` is an
open embedding with conull range for every compatible quotient measure. See the paired Markdown.
-/

noncomputable section

open MeasureTheory Measure Topology Set
open scoped ENNReal NNReal

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.RealLowerBlockChart

open Langlands.GeneralLinear Langlands.QuotientIntegration
open Langlands.RankinSelberg (LeftUnipotentQuotient)
open Langlands.GeneralLinear.RealBruhatTrailingChart (trailingChart trailingDomain coordinateDomain
  upperProjection lowerFactorOfCoordinates upperProjection_apply chartValue isOpen_trailingDomain)

local instance realGLSecondCountable (n : ℕ) :
    SecondCountableTopology (Langlands.GeneralLinear n ℝ) := by
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) ℝ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℝ))
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) ℝ)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

/-! ### The lower triangular factor on the trailing-minor chart -/

section Cell

variable {m : ℕ}

local notation "Mat" => Matrix (Fin m) (Fin m) ℝ

/-- The lower triangular factor `diag(x) · L(x)` of a matrix `y = U(x) L(x)` in the trailing-minor
chart, where `x` are the chart coordinates of `y`. -/
def cellLower (y : Mat) : Mat :=
  Matrix.diagonal (fun i => (trailingChart m).symm y i i) *
    lowerFactorOfCoordinates ((trailingChart m).symm y)

/-- The upper unitriangular factor `U(x) · diag(x)⁻¹`. -/
def cellUpper (y : Mat) : Mat :=
  upperProjection m ((trailingChart m).symm y) *
    Matrix.diagonal (fun i => ((trailingChart m).symm y i i)⁻¹)

theorem symm_mem_coordinateDomain {y : Mat} (hy : y ∈ trailingDomain m) :
    (trailingChart m).symm y ∈ coordinateDomain m :=
  (trailingChart m).map_target hy

theorem cellUpper_mul_cellLower {y : Mat} (hy : y ∈ trailingDomain m) :
    cellUpper y * cellLower y = y := by
  set x := (trailingChart m).symm y
  have hx : ∀ i, x i i ≠ 0 := symm_mem_coordinateDomain hy
  have hD : Matrix.diagonal (fun i => (x i i)⁻¹) * Matrix.diagonal (fun i => x i i) = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    rw [← Matrix.diagonal_one]
    congr 1
    funext i
    exact inv_mul_cancel₀ (hx i)
  have h := (trailingChart m).right_inv hy
  change chartValue x = y at h
  rw [cellUpper, cellLower, Matrix.mul_assoc, ← Matrix.mul_assoc (Matrix.diagonal _), hD,
    Matrix.one_mul]
  exact h

theorem cellUpper_isUpperTriangular (y : Mat) :
    (cellUpper y).IsUpperTriangular := by
  intro i j hij
  have hji : j < i := hij
  simp only [cellUpper, Matrix.mul_diagonal, upperProjection_apply, hji, ite_true, zero_mul]

theorem cellUpper_diag {y : Mat} (hy : y ∈ trailingDomain m) (i : Fin m) :
    cellUpper y i i = 1 := by
  have hx : ∀ i, (trailingChart m).symm y i i ≠ 0 := symm_mem_coordinateDomain hy
  simp only [cellUpper, Matrix.mul_diagonal, upperProjection_apply, lt_irrefl, ite_false]
  exact mul_inv_cancel₀ (hx i)

theorem cellLower_isLowerTriangular (y : Mat) : (cellLower y).IsLowerTriangular := by
  intro i j hij
  have hij' : i < j := hij
  rw [cellLower, Matrix.diagonal_mul, lowerFactorOfCoordinates]
  simp only [Matrix.add_apply, Matrix.sub_apply, upperProjection_apply,
    not_lt_of_gt hij', ite_false, Matrix.one_apply_ne (ne_of_lt hij'), sub_self, zero_add,
    mul_zero]

theorem cellLower_diag {y : Mat} (i : Fin m) :
    cellLower y i i = (trailingChart m).symm y i i := by
  rw [cellLower, Matrix.diagonal_mul, lowerFactorOfCoordinates]
  simp only [Matrix.add_apply, Matrix.sub_apply, upperProjection_apply, lt_irrefl, ite_false,
    Matrix.one_apply_eq, sub_self, add_zero, mul_one]

theorem continuousOn_cellLower : ContinuousOn (cellLower (m := m)) (trailingDomain m) := by
  have hF : Continuous fun x : Mat =>
      Matrix.diagonal (fun i => x i i) * lowerFactorOfCoordinates x := by
    refine Continuous.matrix_mul ?_ ?_
    · exact Continuous.matrix_diagonal (continuous_pi fun i =>
        (continuous_apply_apply i i))
    · exact continuous_const.add (continuous_id.sub (upperProjection m).continuous)
  exact hF.comp_continuousOn (trailingChart m).continuousOn_symm

/-- A lower triangular invertible matrix lies in the chart target and is its own lower factor. -/
theorem lowerTriangular_mem_trailingDomain (b : lowerTriangularSubgroup m ℝ) :
    b.val.val ∈ trailingDomain m ∧ cellLower b.val.val = b.val.val := by
  set B : Mat := b.val.val
  have hlow : B.IsLowerTriangular := b.property
  have hdet : B.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp b.val.isUnit).ne_zero
  have hdiag : ∀ i, B i i ≠ 0 := by
    intro i
    rw [Matrix.det_of_isLowerTriangular B hlow] at hdet
    exact Finset.prod_ne_zero_iff.mp hdet i (Finset.mem_univ i)
  let D : Mat := Matrix.diagonal fun i => B i i
  let Dinv : Mat := Matrix.diagonal fun i => (B i i)⁻¹
  have hDD : D * Dinv = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact mul_inv_cancel₀ (hdiag i)
  let x : Mat := D + (Dinv * B - 1)
  have hentry : ∀ i j, (Dinv * B) i j = (B i i)⁻¹ * B i j := fun i j => by
    simp [Dinv, Matrix.diagonal_mul]
  have hup : upperProjection m x = D := by
    ext i j
    rw [upperProjection_apply]
    by_cases hji : j < i
    · simp only [hji, ite_true]
      simp [D, Matrix.diagonal_apply_ne _ (ne_of_gt hji)]
    · simp only [hji, ite_false]
      rcases (not_lt.mp hji).lt_or_eq with hij | hij
      · have h0 : B i j = 0 := hlow hij
        simp only [x, Matrix.add_apply, Matrix.sub_apply, hentry, h0, mul_zero,
          Matrix.one_apply_ne (ne_of_lt hij), sub_self, add_zero]
      · subst hij
        simp only [x, Matrix.add_apply, Matrix.sub_apply, hentry, inv_mul_cancel₀ (hdiag i),
          Matrix.one_apply_eq, sub_self, add_zero]
  have hlowf : lowerFactorOfCoordinates x = Dinv * B := by
    rw [lowerFactorOfCoordinates, hup]
    simp only [x]
    abel
  have hxd : x ∈ coordinateDomain m := by
    intro i
    have h := congrArg (fun M : Mat => M i i) hup
    simp only [upperProjection_apply, lt_irrefl, ite_false] at h
    rw [h]
    simpa [D] using hdiag i
  have hchart : chartValue x = B := by
    rw [chartValue, hup, hlowf, ← Matrix.mul_assoc, hDD, Matrix.one_mul]
  have hmem : B ∈ trailingDomain m := by
    have := (trailingChart m).map_source hxd
    change chartValue x ∈ trailingDomain m at this
    rwa [hchart] at this
  have hsymm : (trailingChart m).symm B = x := by
    have := (trailingChart m).left_inv hxd
    change (trailingChart m).symm (chartValue x) = x at this
    rwa [hchart] at this
  refine ⟨hmem, ?_⟩
  have hdx : (Matrix.diagonal fun i => x i i) = D := by
    have h := fun i => congrArg (fun M : Mat => M i i) hup
    simp only [upperProjection_apply, lt_irrefl, ite_false] at h
    congr 1
    funext i
    rw [h i]
    simp [D]
  rw [cellLower, hsymm, hdx, hlowf, ← Matrix.mul_assoc, hDD, Matrix.one_mul]

end Cell

section OpenVal

open scoped Matrix.Norms.Operator

theorem isOpen_val_image {m : ℕ} {O : Set (Langlands.GeneralLinear m ℝ)} (hO : IsOpen O) :
    IsOpen (Units.val '' O : Set (Matrix (Fin m) (Fin m) ℝ)) :=
  Units.isOpenEmbedding_val.isOpenMap O hO

end OpenVal

/-! ### The open lower triangular cell -/

section CellMap

variable (m : ℕ)

theorem continuous_lowerTriangularQuotientMap :
    Continuous (lowerTriangularQuotientMap m ℝ) :=
  (leftQuotient_isOpenQuotientMap _).continuous.comp continuous_subtype_val

theorem isOpenMap_lowerTriangularQuotientMap :
    IsOpenMap (lowerTriangularQuotientMap m ℝ) := by
  intro U hU
  obtain ⟨O, hO, rfl⟩ := isOpen_induced_iff.mp hU
  let A : Set (Langlands.GeneralLinear m ℝ) :=
    Units.val ⁻¹' (trailingDomain m ∩ cellLower ⁻¹' (Units.val '' O))
  have hA : IsOpen A :=
    (continuousOn_cellLower.isOpen_inter_preimage (isOpen_trailingDomain m)
      (isOpen_val_image hO)).preimage Units.continuous_val
  have himage : lowerTriangularQuotientMap m ℝ '' (Subtype.val ⁻¹' O) =
      leftQuotientMap (Langlands.GeneralLinear.upperUnipotent m ℝ) '' A := by
    ext q
    constructor
    · rintro ⟨b, hb, rfl⟩
      obtain ⟨hmem, hcell⟩ := lowerTriangular_mem_trailingDomain b
      exact ⟨b.val, ⟨hmem, b.val, hb, hcell.symm⟩, rfl⟩
    · rintro ⟨g, ⟨hg, b, hbO, hb⟩, rfl⟩
      have hblow : b ∈ lowerTriangularSubgroup m ℝ := by
        have h := cellLower_isLowerTriangular g.val
        rw [← hb] at h
        exact h
      refine ⟨⟨b, hblow⟩, hbO, ?_⟩
      change (Quotient.mk _ b : LeftQuotient (Langlands.GeneralLinear.upperUnipotent m ℝ)) =
        Quotient.mk _ g
      rw [leftQuotient_mk_eq_iff]
      have hval : (g * b⁻¹).val = cellUpper g.val := by
        have h := cellUpper_mul_cellLower hg
        rw [← hb] at h
        calc (g * b⁻¹).val = (cellUpper g.val * b.val) * (b⁻¹).val := by rw [h]; rfl
          _ = cellUpper g.val := by rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
      refine ⟨?_, fun i => ?_⟩
      · change (g * b⁻¹).val.IsUpperTriangular
        rw [hval]
        exact cellUpper_isUpperTriangular _
      · change (g * b⁻¹).val i i = 1
        rw [hval]
        exact cellUpper_diag hg i
  rw [himage]
  exact (leftQuotient_isOpenQuotientMap _).isOpenMap A hA

/-- Over `ℝ`, the coset map `B⁻_m → N_m \ GL_m(ℝ)` is an open embedding. -/
theorem isOpenEmbedding_lowerTriangularQuotientMap :
    IsOpenEmbedding (lowerTriangularQuotientMap m ℝ) :=
  .of_continuous_injective_isOpenMap (continuous_lowerTriangularQuotientMap m)
    lowerTriangularQuotientMap_injective (isOpenMap_lowerTriangularQuotientMap m)

end CellMap

/-! ### Compatible quotient measures on the cell -/

section Measures

open ArchimedeanLocal

attribute [local instance] archimedeanRealGLMeasurable archimedeanRealGLBorel
  archimedeanRealNMeasurable archimedeanRealNBorel archimedeanRealQMeasurable
  archimedeanRealQBorel

local instance lowerTriangularMeasurable (m : ℕ) :
    MeasurableSpace (lowerTriangularSubgroup m ℝ) := borel _
local instance lowerTriangularBorel (m : ℕ) : BorelSpace (lowerTriangularSubgroup m ℝ) := ⟨rfl⟩

variable {n : ℕ}

theorem exists_mem_nhds_ne_zero : ∀ U ∈ 𝓝 (0 : ℝ), ∃ t ∈ U, t ≠ 0 := by
  intro U hU
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨ε / 2, hball ?_, by positivity⟩
  rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
  linarith

/-- The cosets with no lower triangular representative form a null set for every compatible
quotient measure on `N_(n+1) \ GL_(n+1)(ℝ)`. -/
theorem range_compl_null (D : RealQuotientMeasureData n) :
    D.measure (range (lowerTriangularQuotientMap (n + 1) ℝ))ᶜ = 0 := by
  have := D.groupHaar_isHaar
  have := D.unipotentHaar_isHaar
  have := D.unipotentHaar_rightInvariant
  set N := Langlands.GeneralLinear.upperUnipotent (n + 1) ℝ
  set S := (range (lowerTriangularQuotientMap (n + 1) ℝ))ᶜ
  have hSm : MeasurableSet S :=
    (isOpenEmbedding_lowerTriangularQuotientMap (n + 1)).isOpen_range.isClosed_compl.measurableSet
  have hπ : Measurable (leftQuotientMap N) := continuous_quotient_mk'.measurable
  have hpre : leftQuotientMap N ⁻¹' S = {g : Langlands.GeneralLinear (n + 1) ℝ |
      ¬ ∃ u ∈ N, ∃ b ∈ lowerTriangularSubgroup (n + 1) ℝ, u * b = g} := by
    ext g
    simp only [S, mem_preimage, mem_compl_iff, mem_range, leftQuotientMap_apply,
      lowerTriangularQuotientMap_apply, Subtype.exists, mem_ofPred_eq]
    refine not_congr ⟨fun ⟨b, hb, hbg⟩ => ⟨g * b⁻¹, (leftQuotient_mk_eq_iff N b g).mp hbg, b, hb,
      by group⟩, fun ⟨u, hu, b, hb, hub⟩ => ⟨b, hb, (leftQuotient_mk_eq_iff N b g).mpr ?_⟩⟩
    rw [← hub, mul_inv_cancel_right]
    exact hu
  have hnull : D.groupHaar (leftQuotientMap N ⁻¹' S) = 0 := by
    have : D.groupHaar.Regular := inferInstance
    have : SigmaFinite D.groupHaar := inferInstance
    have : D.groupHaar.InnerRegular := inferInstance
    rw [hpre]
    exact haar_setOf_not_upperUnipotent_mul_lowerTriangular exists_mem_nhds_ne_zero D.groupHaar
  have hW := D.compatible.lintegral_eq_lintegral_quotientAverageENNReal
    (RealIwasawa.isClosed_upperUnipotent (n := n + 1))
    ((leftQuotientMap N ⁻¹' S).indicator 1) (measurable_one.indicator (hπ hSm))
  rw [lintegral_indicator_one (hπ hSm), hnull] at hW
  have havg : quotientAverageENNReal N D.unipotentHaar ((leftQuotientMap N ⁻¹' S).indicator 1) =
      fun q => S.indicator (1 : LeftQuotient N → ℝ≥0∞) q * D.unipotentHaar univ := by
    funext q
    induction q using Quotient.inductionOn with
    | h g =>
      rw [quotientAverageENNReal_mk]
      have hc : ∀ h : N, (leftQuotientMap N ⁻¹' S).indicator
          (1 : Langlands.GeneralLinear (n + 1) ℝ → ℝ≥0∞) (h.val * g) =
          S.indicator (1 : LeftQuotient N → ℝ≥0∞) (Quotient.mk _ g) := by
        intro h
        have hq : (Quotient.mk _ (h.val * g) : LeftQuotient N) = Quotient.mk _ g :=
          (leftQuotient_mk_eq_iff N _ _).mpr (by simp)
        change S.indicator (1 : LeftQuotient N → ℝ≥0∞) (leftQuotientMap N (h.val * g)) = _
        rw [leftQuotientMap_apply, hq]
      rw [lintegral_congr hc, lintegral_const]
  rw [havg, lintegral_mul_const _ (measurable_one.indicator hSm), lintegral_indicator_one hSm]
    at hW
  have hne : D.unipotentHaar univ ≠ 0 := (measure_univ_pos.mpr (NeZero.ne _)).ne'
  exact (mul_eq_zero.mp hW.symm).resolve_right hne

theorem lowerTriangularQuotientMap_mul' {m : ℕ} (b c : lowerTriangularSubgroup m ℝ) :
    lowerTriangularQuotientMap m ℝ (b * c) =
      rightTranslate (Langlands.GeneralLinear.upperUnipotent m ℝ) c.val
        (lowerTriangularQuotientMap m ℝ b) := rfl

theorem measurableEmbedding_lowerTriangularQuotientMap (m : ℕ) :
    MeasurableEmbedding (lowerTriangularQuotientMap (m + 1) ℝ) :=
  (isOpenEmbedding_lowerTriangularQuotientMap (m + 1)).measurableEmbedding

/-- The pullback of a compatible quotient measure to the lower triangular group is right
invariant, finite on compacts, σ-finite and nonzero, and pushes forward to the quotient
measure. -/
theorem comap_properties (D : RealQuotientMeasureData n) :
    let ρ := D.measure.comap (lowerTriangularQuotientMap (n + 1) ℝ)
    ρ.IsMulRightInvariant ∧ IsFiniteMeasureOnCompacts ρ ∧ SigmaFinite ρ ∧ ρ ≠ 0 ∧
      ρ.map (lowerTriangularQuotientMap (n + 1) ℝ) = D.measure := by
  intro ρ
  have := D.groupHaar_isHaar
  have := D.unipotentHaar_isHaar
  have := D.unipotentHaar_rightInvariant
  have := D.compatible.regular
  have hβ := measurableEmbedding_lowerTriangularQuotientMap n
  have hβc : Continuous (lowerTriangularQuotientMap (n + 1) ℝ) :=
    continuous_lowerTriangularQuotientMap (n + 1)
  have hinv : ρ.IsMulRightInvariant := by
    refine ⟨fun c => ?_⟩
    ext S hS
    rw [Measure.map_apply (measurable_mul_const c) hS, hβ.comap_apply, hβ.comap_apply]
    have himage : lowerTriangularQuotientMap (n + 1) ℝ '' ((fun x => x * c) ⁻¹' S) =
        rightTranslate (Langlands.GeneralLinear.upperUnipotent (n + 1) ℝ) c.val ⁻¹'
          (lowerTriangularQuotientMap (n + 1) ℝ '' S) := by
      ext q
      constructor
      · rintro ⟨b, hb, rfl⟩
        exact ⟨b * c, hb, rfl⟩
      · rintro ⟨b, hb, hq⟩
        refine ⟨b * c⁻¹, by simpa using hb, ?_⟩
        have := congrArg (rightTranslate (Langlands.GeneralLinear.upperUnipotent (n + 1) ℝ)
          c⁻¹.val) hq
        rw [← lowerTriangularQuotientMap_mul', rightTranslate_mul] at this
        simpa using this
    rw [himage]
    exact (D.compatible.right_invariant c.val).measure_preimage
      (hβ.measurableSet_image.mpr hS).nullMeasurableSet
  have hfin : IsFiniteMeasureOnCompacts ρ := by
    refine ⟨fun K hK => ?_⟩
    rw [hβ.comap_apply]
    exact (hK.image hβc).measure_lt_top
  have hmap : ρ.map (lowerTriangularQuotientMap (n + 1) ℝ) = D.measure := by
    rw [hβ.map_comap]
    exact Measure.restrict_eq_self_of_ae_mem (measure_eq_zero_iff_ae_notMem.mp
      (range_compl_null D) |>.mono fun q hq => by simpa using hq)
  have : SecondCountableTopology (lowerTriangularSubgroup (n + 1) ℝ) :=
    IsEmbedding.subtypeVal.secondCountableTopology
  have : LocallyCompactSpace (lowerTriangularSubgroup (n + 1) ℝ) :=
    (lowerTriangularSubgroup_isClosed (n + 1)).locallyCompactSpace
  refine ⟨hinv, hfin, inferInstance, ?_, hmap⟩
  intro h0
  exact D.compatible.nonzero (by rw [← hmap, h0, Measure.map_zero])

/-! ### The determinant-weighted product in lower-block coordinates -/

open RealUnequalMellinReduction (quotientDetAbs quotientDetAbs_pos continuous_quotientDetAbs)

private theorem map_withDensity_equiv_of_preserving
    {A : Type*} [MeasurableSpace A] (μ : Measure A) (e : A ≃ᵐ A)
    (he : MeasurePreserving e μ μ) (w : A → ℝ≥0∞) :
    Measure.map e (μ.withDensity w) = μ.withDensity (w ∘ e.symm) := by
  ext s hs
  rw [Measure.map_apply e.measurable hs, withDensity_apply _ (e.measurable hs),
    withDensity_apply _ hs]
  simpa only [Function.comp_apply, e.symm_apply_apply] using
    he.setLIntegral_comp_preimage_emb e.measurableEmbedding (w ∘ e.symm) s

variable (n)

/-- The density `|det b|⁻¹` on the invertible lower triangular matrices. -/
def lowerDensity (b : lowerTriangularSubgroup (n + 1) ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal |b.val.val.det|⁻¹

/-- The density `|det g|⁻¹` on `N_(n+1) \ GL_(n+1)(ℝ)`. -/
def quotientDensity (q : LeftUnipotentQuotient n ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (quotientDetAbs q)⁻¹

/-- Lebesgue measure on the row space `M_(1×(n+1))(ℝ)`. -/
def rowMeasure : Measure (Matrix (Fin 1) (Fin (n + 1)) ℝ) :=
  (volume : Measure (Fin 1 → Fin (n + 1) → ℝ))

variable {n}

theorem det_ne_zero (g : Langlands.GeneralLinear (n + 1) ℝ) : g.val.det ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det _).mp g.isUnit).ne_zero

theorem det_inv_val {m : ℕ} (u : Langlands.GeneralLinear m ℝ) :
    (u⁻¹).val.det = (u.val.det)⁻¹ := by
  have h : (u⁻¹).val.det * u.val.det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]
  exact eq_inv_of_mul_eq_one_left h

theorem quotientDetAbs_mk (g : Langlands.GeneralLinear (n + 1) ℝ) :
    quotientDetAbs (Quotient.mk _ g : LeftUnipotentQuotient n ℝ) = |g.val.det| := by
  have h := (Quotient.mk_out (s := QuotientGroup.rightRel
    (Langlands.GeneralLinear.upperUnipotent (n + 1) ℝ)) g)
  rw [QuotientGroup.rightRel_apply] at h
  change |(Quotient.out (Quotient.mk _ g : LeftUnipotentQuotient n ℝ)).val.det| = _
  set o := Quotient.out (Quotient.mk _ g : LeftUnipotentQuotient n ℝ)
  have hdet := Langlands.RankinSelberg.unipotent_det (F := ℝ) ⟨g * o⁻¹, h⟩
  change (g * o⁻¹).val.det = 1 at hdet
  have : o = (g * o⁻¹)⁻¹ * g := by group
  rw [this, Units.val_mul, Matrix.det_mul, det_inv_val, hdet, inv_one, one_mul]

theorem continuous_lowerDensity : Continuous (lowerDensity n) :=
  ENNReal.continuous_ofReal.comp ((Units.continuous_val.comp
    continuous_subtype_val).matrix_det.abs.inv₀ fun b => abs_ne_zero.mpr (det_ne_zero b.val))

theorem continuous_quotientDensity : Continuous (quotientDensity n) :=
  ENNReal.continuous_ofReal.comp (continuous_quotientDetAbs.inv₀ fun q =>
    (quotientDetAbs_pos q).ne')

theorem map_lowerDensity_mulRight (ρ : Measure (lowerTriangularSubgroup (n + 1) ℝ))
    [ρ.IsMulRightInvariant] (g : lowerTriangularSubgroup (n + 1) ℝ) :
    Measure.map (fun b => b * g) (ρ.withDensity (lowerDensity n)) =
      ENNReal.ofReal |g.val.val.det| • ρ.withDensity (lowerDensity n) := by
  change Measure.map (MeasurableEquiv.mulRight g) (ρ.withDensity (lowerDensity n)) = _
  rw [map_withDensity_equiv_of_preserving ρ (MeasurableEquiv.mulRight g)
    (measurePreserving_mul_right ρ g)]
  have hweight : lowerDensity n ∘ (MeasurableEquiv.mulRight g).symm =
      ENNReal.ofReal |g.val.val.det| • lowerDensity n := by
    funext b
    change lowerDensity n (b * g⁻¹) = ENNReal.ofReal |g.val.val.det| * lowerDensity n b
    rw [lowerDensity, lowerDensity, ← ENNReal.ofReal_mul (abs_nonneg _)]
    congr 1
    have hginv : ((g.val)⁻¹).val.det = (g.val.val.det)⁻¹ := by
      exact det_inv_val g.val
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Matrix.det_mul, abs_mul,
      mul_inv]
    rw [hginv, abs_inv, inv_inv]
    ring
  rw [hweight, withDensity_smul _ (continuous_lowerDensity).measurable]

theorem map_rowMeasure_mulRight (g : Langlands.GeneralLinear (n + 1) ℝ) :
    Measure.map (fun X : Matrix (Fin 1) (Fin (n + 1)) ℝ =>
        X * (g.val : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)) (rowMeasure n) =
      ENNReal.ofReal |g.val.det|⁻¹ • rowMeasure n := by
  let e := MeasurableEquiv.funUnique (Fin 1) (Fin (n + 1) → ℝ)
  have he : MeasurePreserving e volume volume := volume_preserving_funUnique _ _
  have hdet : (g.val.transpose).det ≠ 0 := by rw [Matrix.det_transpose]; exact det_ne_zero g
  have h2 : ∀ v : Fin (n + 1) → ℝ, e.symm v 0 = v := fun _ => rfl
  have hfun : (fun X : Matrix (Fin 1) (Fin (n + 1)) ℝ =>
      X * (g.val : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)) =
      e.symm ∘ (Matrix.toLin' g.val.transpose) ∘ e := by
    funext X
    ext i j
    fin_cases i
    change (X * (g.val : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)) 0 j =
      e.symm (Matrix.toLin' g.val.transpose (X 0)) 0 j
    rw [h2, Matrix.toLin'_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct]
    simp only [Matrix.transpose_apply, mul_comm]
  rw [hfun, rowMeasure]
  change Measure.map (e.symm ∘ (Matrix.toLin' g.val.transpose) ∘ e)
      (volume : Measure (Fin 1 → Fin (n + 1) → ℝ)) =
    ENNReal.ofReal |g.val.det|⁻¹ • (volume : Measure (Fin 1 → Fin (n + 1) → ℝ))
  rw [← Measure.map_map e.symm.measurable
      ((Matrix.toLin' g.val.transpose).continuous_of_finiteDimensional.measurable.comp
        e.measurable),
    ← Measure.map_map (Matrix.toLin' g.val.transpose).continuous_of_finiteDimensional.measurable
      e.measurable, he.map_eq, Real.map_matrix_volume_pi_eq_smul_volume_pi hdet,
    Measure.map_smul, he.symm.map_eq, Matrix.det_transpose, abs_inv]
  exact e.symm.measurable.aemeasurable

variable (n) in
/-- Right multiplication by `diag(g, h)` in block coordinates preserves the weighted product. -/
theorem measurePreserving_diagonal
    (ρa : Measure (lowerTriangularSubgroup (n + 1) ℝ)) [SFinite ρa] [ρa.IsMulRightInvariant]
    (ρd : Measure (lowerTriangularSubgroup 1 ℝ)) [SFinite ρd] [ρd.IsMulRightInvariant]
    (g : lowerTriangularSubgroup (n + 1) ℝ) (h : lowerTriangularSubgroup 1 ℝ) :
    MeasurePreserving
      (fun z : lowerTriangularSubgroup (n + 1) ℝ × Matrix (Fin 1) (Fin (n + 1)) ℝ ×
          lowerTriangularSubgroup 1 ℝ => (z.1 * g, z.2.1 * g.val.val, z.2.2 * h))
      ((ρa.withDensity (lowerDensity n)).prod ((rowMeasure n).prod ρd))
      ((ρa.withDensity (lowerDensity n)).prod ((rowMeasure n).prod ρd)) := by
  have hXm : Measurable (fun X : Matrix (Fin 1) (Fin (n + 1)) ℝ => X * g.val.val) :=
    (continuous_id.matrix_mul continuous_const).measurable
  have : SFinite (rowMeasure n) := inferInstanceAs (SFinite (volume : Measure (Fin 1 → _)))
  change MeasurePreserving
    (Prod.map (fun b => b * g) (Prod.map (fun X => X * g.val.val) (fun b => b * h))) _ _
  refine ⟨(measurable_mul_const g).prodMap (hXm.prodMap (measurable_mul_const h)), ?_⟩
  rw [← map_prod_map _ _ (measurable_mul_const g) (hXm.prodMap (measurable_mul_const h)),
    ← map_prod_map _ _ hXm (measurable_mul_const h), map_lowerDensity_mulRight,
    map_rowMeasure_mulRight, map_mul_right_eq_self]
  rw [prod_smul_left, prod_smul_left, prod_smul_right, smul_smul,
    ← ENNReal.ofReal_mul (abs_nonneg _), mul_inv_cancel₀ (abs_ne_zero.mpr (det_ne_zero g.val)),
    ENNReal.ofReal_one, one_smul]

variable (n) in
/-- A translation of the row coordinate depending on the last block preserves the weighted
product. -/
theorem measurePreserving_shear
    (ρa : Measure (lowerTriangularSubgroup (n + 1) ℝ)) [SFinite ρa]
    (ρd : Measure (lowerTriangularSubgroup 1 ℝ)) [SFinite ρd]
    (y : Matrix (Fin 1) (Fin (n + 1)) ℝ) :
    MeasurePreserving
      (fun z : lowerTriangularSubgroup (n + 1) ℝ × Matrix (Fin 1) (Fin (n + 1)) ℝ ×
          lowerTriangularSubgroup 1 ℝ => (z.1, z.2.1 + z.2.2.val.val * y, z.2.2))
      ((ρa.withDensity (lowerDensity n)).prod ((rowMeasure n).prod ρd))
      ((ρa.withDensity (lowerDensity n)).prod ((rowMeasure n).prod ρd)) := by
  have : SFinite (rowMeasure n) := inferInstanceAs (SFinite (volume : Measure (Fin 1 → _)))
  have : (rowMeasure n).IsAddRightInvariant :=
    inferInstanceAs ((volume : Measure (Fin 1 → Fin (n + 1) → ℝ)).IsAddRightInvariant)
  have : SecondCountableTopology (lowerTriangularSubgroup 1 ℝ) :=
    IsEmbedding.subtypeVal.secondCountableTopology
  have hsm : Measurable
      (Function.uncurry fun (b : lowerTriangularSubgroup 1 ℝ)
        (X : Matrix (Fin 1) (Fin (n + 1)) ℝ) => X + b.val.val * y) :=
    (continuous_snd.add
      ((Units.continuous_val.comp (continuous_subtype_val.comp continuous_fst)).matrix_mul
        continuous_const)).measurable
  have hs := (MeasurePreserving.id ρd).skew_product hsm
    (Filter.Eventually.of_forall fun b =>
      (measurePreserving_add_right (rowMeasure n) (b.val.val * y)).map_eq)
  have hs' : MeasurePreserving
      (fun z : Matrix (Fin 1) (Fin (n + 1)) ℝ × lowerTriangularSubgroup 1 ℝ =>
        (z.1 + z.2.val.val * y, z.2))
      ((rowMeasure n).prod ρd) ((rowMeasure n).prod ρd) :=
    measurePreserving_swap.comp (hs.comp measurePreserving_swap)
  exact (MeasurePreserving.id _).prod hs'

variable (n) in
/-- Right multiplication in block coordinates preserves the weighted product. -/
theorem measurePreserving_mulRight
    (ρa : Measure (lowerTriangularSubgroup (n + 1) ℝ)) [SFinite ρa] [ρa.IsMulRightInvariant]
    (ρd : Measure (lowerTriangularSubgroup 1 ℝ)) [SFinite ρd] [ρd.IsMulRightInvariant]
    (g : lowerTriangularSubgroup (n + 1) ℝ) (y : Matrix (Fin 1) (Fin (n + 1)) ℝ)
    (h : lowerTriangularSubgroup 1 ℝ) :
    MeasurePreserving
      (fun z : lowerTriangularSubgroup (n + 1) ℝ × Matrix (Fin 1) (Fin (n + 1)) ℝ ×
          lowerTriangularSubgroup 1 ℝ =>
        (z.1 * g, z.2.1 * g.val.val + z.2.2.val.val * y, z.2.2 * h))
      ((ρa.withDensity (lowerDensity n)).prod ((rowMeasure n).prod ρd))
      ((ρa.withDensity (lowerDensity n)).prod ((rowMeasure n).prod ρd)) := by
  convert (measurePreserving_diagonal n ρa ρd g h).comp
    (measurePreserving_shear n ρa ρd (y * g.val.inv)) using 1
  funext z
  simp only [Function.comp_apply, Matrix.add_mul, Matrix.mul_assoc, g.val.inv_val,
    Matrix.mul_one]

/-! ### Comparison of quotient measures in lower-block coordinates -/

theorem quotientDensity_cell (b : lowerTriangularSubgroup (n + 1) ℝ) :
    quotientDensity n (lowerTriangularQuotientMap (n + 1) ℝ b) = lowerDensity n b := by
  rw [quotientDensity, lowerDensity, lowerTriangularQuotientMap_apply]
  change ENNReal.ofReal (quotientDetAbs (Quotient.mk _ b.val : LeftUnipotentQuotient n ℝ))⁻¹ = _
  rw [quotientDetAbs_mk]

/-- Every compatible quotient measure on `N_(n+2) \ GL_(n+2)(ℝ)` is a positive multiple of the
pushforward along `([g], x, h) ↦ [[[g, 0], [x, h]]]` of `|det g|⁻¹ dD(g) dx dρ(h)`, for any
compatible quotient measure `D` on `N_(n+1) \ GL_(n+1)(ℝ)` and any nonzero right-invariant
measure `ρ` on the invertible lower triangular `1 × 1` matrices, σ-finite and finite on
compacts. -/
theorem chart_eq_smul_map (D : RealQuotientMeasureData n) (D' : RealQuotientMeasureData (n + 1))
    (ρ : Measure (lowerTriangularSubgroup 1 ℝ)) [SigmaFinite ρ] [IsFiniteMeasureOnCompacts ρ]
    [ρ.IsMulRightInvariant] (hρ : ρ ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ D'.measure = ENNReal.ofReal C •
      Measure.map (lowerBlockQuotientChart (a := n + 1) (d := 1) (R := ℝ))
        ((D.measure.withDensity (quotientDensity n)).prod ((rowMeasure n).prod ρ)) := by
  have : SecondCountableTopology (lowerTriangularSubgroup (n + 1) ℝ) :=
    IsEmbedding.subtypeVal.secondCountableTopology
  have : SecondCountableTopology (lowerTriangularSubgroup 1 ℝ) :=
    IsEmbedding.subtypeVal.secondCountableTopology
  have : SecondCountableTopology (lowerTriangularSubgroup (n + 1 + 1) ℝ) :=
    IsEmbedding.subtypeVal.secondCountableTopology
  have : LocallyCompactSpace (lowerTriangularSubgroup (n + 1 + 1) ℝ) :=
    (lowerTriangularSubgroup_isClosed (n + 1 + 1)).locallyCompactSpace
  have : SecondCountableTopology (LeftUnipotentQuotient n ℝ) :=
    (leftQuotient_isOpenQuotientMap _).secondCountableTopology
  have : LocallyCompactSpace (lowerTriangularSubgroup (n + 1) ℝ) :=
    (lowerTriangularSubgroup_isClosed (n + 1)).locallyCompactSpace
  have : SFinite (rowMeasure n) := inferInstanceAs (SFinite (volume : Measure (Fin 1 → _)))
  have : IsFiniteMeasureOnCompacts (rowMeasure n) :=
    inferInstanceAs (IsFiniteMeasureOnCompacts (volume : Measure (Fin 1 → Fin (n + 1) → ℝ)))
  have : (rowMeasure n).IsOpenPosMeasure :=
    inferInstanceAs ((volume : Measure (Fin 1 → Fin (n + 1) → ℝ)).IsOpenPosMeasure)
  obtain ⟨hρa_inv, hρa_fin, hρa_sf, hρa_ne, hρa_map⟩ := comap_properties D
  obtain ⟨hρad_inv, hρad_fin, -, hρad_ne, hρad_map⟩ := comap_properties D'
  set ρa := D.measure.comap (lowerTriangularQuotientMap (n + 1) ℝ) with hρa_def
  set ρad := D'.measure.comap (lowerTriangularQuotientMap (n + 1 + 1) ℝ) with hρad_def
  set w := lowerDensity n with hw_def
  set dx := rowMeasure n with hdx_def
  set θ := lowerTriangularBlockMap (n + 1) 1 ℝ with hθ_def
  have hβa : Measurable (lowerTriangularQuotientMap (n + 1) ℝ) :=
    (measurableEmbedding_lowerTriangularQuotientMap n).measurable
  have hβad : Measurable (lowerTriangularQuotientMap (n + 1 + 1) ℝ) :=
    (measurableEmbedding_lowerTriangularQuotientMap (n + 1)).measurable
  have hθm : Measurable θ := continuous_lowerTriangularBlockMap.measurable
  have hchart : Measurable (lowerBlockQuotientChart (a := n + 1) (d := 1) (R := ℝ)) :=
    continuous_lowerBlockQuotientChart.measurable
  have hw : Continuous w := continuous_lowerDensity
  have hwtop : ∀ b, w b ≠ ∞ := fun b => ENNReal.ofReal_ne_top
  have hw0 : ∀ b, w b ≠ 0 := fun b => by
    rw [hw_def, lowerDensity, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact inv_pos.mpr (abs_pos.mpr (det_ne_zero b.val))
  have hdens : D.measure.withDensity (quotientDensity n) =
      (ρa.withDensity w).map (lowerTriangularQuotientMap (n + 1) ℝ) := by
    rw [← hρa_map]
    ext s hs
    rw [withDensity_apply _ hs, Measure.map_apply hβa hs, withDensity_apply _ (hβa hs),
      setLIntegral_map hs continuous_quotientDensity.measurable hβa]
    refine setLIntegral_congr_fun (hβa hs) (fun b _ => ?_)
    exact quotientDensity_cell b
  set P := (ρa.withDensity w).prod (dx.prod ρ) with hP_def
  have hcomp : lowerBlockQuotientChart ∘ Prod.map (lowerTriangularQuotientMap (n + 1) ℝ) id =
      lowerTriangularQuotientMap (n + 1 + 1) ℝ ∘ θ := by
    funext z
    rfl
  have hmapchart : Measure.map (lowerBlockQuotientChart (a := n + 1) (d := 1) (R := ℝ))
      ((D.measure.withDensity (quotientDensity n)).prod (dx.prod ρ)) =
      (P.map θ).map (lowerTriangularQuotientMap (n + 1 + 1) ℝ) := by
    rw [hdens, ← Measure.map_id (μ := dx.prod ρ), map_prod_map _ _ hβa measurable_id,
      Measure.map_map hchart (hβa.prodMap measurable_id), hcomp,
      ← Measure.map_map hβad hθm]
  have hνinv : (P.map θ).IsMulRightInvariant := by
    refine ⟨fun c => ?_⟩
    obtain ⟨v, rfl⟩ := (lowerTriangularBlockEquiv (n + 1) 1 ℝ).surjective c
    have hφ := measurePreserving_mulRight n ρa ρ v.1 v.2.1 v.2.2
    rw [Measure.map_map (measurable_mul_const _) hθm]
    have hfun : (fun k => k * lowerTriangularBlockEquiv (n + 1) 1 ℝ v) ∘ θ =
        θ ∘ (fun z : lowerTriangularSubgroup (n + 1) ℝ ×
            Matrix (Fin 1) (Fin (n + 1)) ℝ × lowerTriangularSubgroup 1 ℝ =>
          (z.1 * v.1, z.2.1 * v.1.val.val + z.2.2.val.val * v.2.1, z.2.2 * v.2.2)) := by
      funext z
      exact lowerTriangularBlockMap_mul z v
    rw [hfun, ← Measure.map_map hθm hφ.measurable, hφ.map_eq]
  have : IsFiniteMeasureOnCompacts ρa := hρa_fin
  have hAloc : IsLocallyFiniteMeasure (ρa.withDensity w) := by
    have hA : ρa.withDensity w = ρa.withDensity fun b => ((w b).toNNReal : ℝ≥0∞) :=
      congrArg _ (funext fun b => (ENNReal.coe_toNNReal (hwtop b)).symm)
    rw [hA]
    exact IsLocallyFiniteMeasure.withDensity_coe
      (ENNReal.continuousOn_toNNReal.comp_continuous hw hwtop)
  have : IsFiniteMeasureOnCompacts ρa := hρa_fin
  have : IsFiniteMeasureOnCompacts (ρa.withDensity w) := inferInstance
  have : SigmaFinite ρa := hρa_sf
  have hνfin : IsFiniteMeasureOnCompacts (P.map θ) := by
    refine ⟨fun K hK => ?_⟩
    rw [Measure.map_apply hθm hK.measurableSet]
    exact ((lowerTriangularBlockHomeomorph (n + 1) 1 ℝ).isCompact_preimage.mpr hK).measure_lt_top
  have hAne : ρa.withDensity w ≠ 0 := by
    intro h0
    rw [withDensity_eq_zero_iff hw.measurable.aemeasurable] at h0
    exact hρa_ne (ae_eq_bot.mp (Filter.eventually_false_iff_eq_bot.mp
      (h0.mono fun b hb => hw0 b hb)))
  have hdxne : dx ≠ 0 := by
    intro h0
    have := (isOpen_univ.measure_pos dx ⟨0, trivial⟩).ne'
    rw [h0] at this
    exact this rfl
  have hPne : P ≠ 0 := by
    intro h0
    have h := congrArg (fun ν : Measure _ => ν (univ ×ˢ (univ ×ˢ univ))) h0
    simp only [hP_def, Measure.prod_prod, Measure.coe_zero, Pi.zero_apply, mul_eq_zero,
      Measure.measure_univ_eq_zero] at h
    rcases h with h | h | h
    exacts [hAne h, hdxne h, hρ h]
  have hνne : P.map θ ≠ 0 := fun h0 => hPne ((Measure.map_eq_zero_iff hθm.aemeasurable).mp h0)
  obtain ⟨C, hC, hCeq⟩ := Langlands.RankinSelberg.exists_pos_smul_eq_of_isMulRightInvariant ρad
    (P.map θ) hρad_ne hνne
  refine ⟨C, hC, ?_⟩
  rw [hmapchart, ← Measure.map_smul, ← hCeq, hρad_map]
  exact hβad.aemeasurable

/-! ### Coordinates `(x, u) ∈ ℝ^(n+1) × ℝˣ` for the last row -/

theorem fin_one_not_lt (i j : Fin 1) : ¬ i < j := by
  rw [Subsingleton.elim i j]
  exact lt_irrefl j

attribute [local instance] RealRankZero.unitsMeasurable RealRankZero.unitsBorel

/-- A nonzero real number as an invertible `1 × 1` matrix. -/
def unitsGL (u : ℝˣ) : Langlands.GeneralLinear 1 ℝ :=
  Units.mk (Matrix.of fun _ _ => (u : ℝ) : Matrix (Fin 1) (Fin 1) ℝ)
    (Matrix.of fun _ _ => ((u⁻¹ : ℝˣ) : ℝ) : Matrix (Fin 1) (Fin 1) ℝ)
    (by ext i j; fin_cases i; fin_cases j; simp [Matrix.mul_apply])
    (by ext i j; fin_cases i; fin_cases j; simp [Matrix.mul_apply])

/-- A nonzero real number as an invertible lower triangular `1 × 1` matrix. -/
def unitsLower (u : ℝˣ) : lowerTriangularSubgroup 1 ℝ :=
  ⟨unitsGL u, fun i j h => absurd h (fin_one_not_lt i j)⟩

@[simp] theorem unitsLower_val (u : ℝˣ) (i j : Fin 1) : (unitsLower u).val.val i j = u := rfl

theorem unitsLower_mul (u v : ℝˣ) : unitsLower (u * v) = unitsLower u * unitsLower v := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  fin_cases i; fin_cases j
  simp [unitsLower, unitsGL, Matrix.mul_apply]

theorem continuous_unitsGL : Continuous unitsGL := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · exact continuous_matrix fun _ _ => Units.continuous_val
  · exact continuous_matrix fun _ _ => Units.continuous_coe_inv

/-- The entry of an invertible `1 × 1` matrix. -/
def lowerUnits (b : lowerTriangularSubgroup 1 ℝ) : ℝˣ :=
  ⟨b.val.val 0 0, b.val.inv 0 0,
    by
      have h := congrArg (fun M : Matrix (Fin 1) (Fin 1) ℝ => M 0 0) b.val.val_inv
      simpa [Matrix.mul_apply] using h,
    by
      have h := congrArg (fun M : Matrix (Fin 1) (Fin 1) ℝ => M 0 0) b.val.inv_val
      simpa [Matrix.mul_apply] using h⟩

/-- `ℝˣ ≃ₜ B⁻₁(ℝ)`. -/
def unitsLowerHomeomorph : ℝˣ ≃ₜ lowerTriangularSubgroup 1 ℝ where
  toFun := unitsLower
  invFun := lowerUnits
  left_inv u := by
    apply Units.ext
    rfl
  right_inv b := by
    apply Subtype.ext
    apply Units.ext
    ext i j
    fin_cases i; fin_cases j
    rfl
  continuous_toFun := continuous_unitsGL.subtype_mk _
  continuous_invFun := by
    refine Units.continuous_iff.mpr ⟨?_, ?_⟩
    · exact (Units.continuous_val.comp
        (continuous_subtype_val (p := fun g => g ∈ lowerTriangularSubgroup 1 ℝ))).matrix_elem 0 0
    · exact (Units.continuous_coe_inv.comp
        (continuous_subtype_val (p := fun g => g ∈ lowerTriangularSubgroup 1 ℝ))).matrix_elem 0 0

/-- The right Haar measure `|u|⁻¹ du` transported to `B⁻₁(ℝ)`. -/
def lowerHaar : Measure (lowerTriangularSubgroup 1 ℝ) :=
  RealRankZero.unitsHaar.map unitsLower

theorem measurable_unitsLower : Measurable unitsLower :=
  unitsLowerHomeomorph.continuous.measurable

instance lowerHaar_isMulRightInvariant : lowerHaar.IsMulRightInvariant := by
  refine ⟨fun c => ?_⟩
  rw [lowerHaar, Measure.map_map (measurable_mul_const c) measurable_unitsLower]
  have hfun : (fun b => b * c) ∘ unitsLower = unitsLower ∘ (fun u => u * lowerUnits c) := by
    funext u
    change unitsLower u * c = unitsLower (u * lowerUnits c)
    rw [unitsLower_mul]
    congr 1
    exact (unitsLowerHomeomorph.right_inv c).symm
  rw [hfun, ← Measure.map_map measurable_unitsLower (measurable_mul_const _),
    map_mul_right_eq_self]

instance lowerHaar_isFiniteMeasureOnCompacts : IsFiniteMeasureOnCompacts lowerHaar := by
  refine ⟨fun K hK => ?_⟩
  rw [lowerHaar, Measure.map_apply measurable_unitsLower hK.measurableSet]
  exact (unitsLowerHomeomorph.isCompact_preimage.mpr hK).measure_lt_top

instance lowerHaar_sigmaFinite : SigmaFinite lowerHaar := by
  have : SecondCountableTopology (lowerTriangularSubgroup 1 ℝ) :=
    IsEmbedding.subtypeVal.secondCountableTopology
  have : LocallyCompactSpace (lowerTriangularSubgroup 1 ℝ) :=
    (lowerTriangularSubgroup_isClosed 1).locallyCompactSpace
  infer_instance

theorem lowerHaar_ne_zero : lowerHaar ≠ 0 := by
  rw [lowerHaar, Ne, Measure.map_eq_zero_iff measurable_unitsLower.aemeasurable]
  exact NeZero.ne _

/-- The row `x` as a `1 × (n+1)` matrix. -/
def rowEquiv : (Fin (n + 1) → ℝ) ≃ᵐ Matrix (Fin 1) (Fin (n + 1)) ℝ :=
  (MeasurableEquiv.funUnique (Fin 1) (Fin (n + 1) → ℝ)).symm

theorem map_rowEquiv : (volume : Measure (Fin (n + 1) → ℝ)).map rowEquiv = rowMeasure n :=
  (volume_preserving_funUnique (Fin 1) (Fin (n + 1) → ℝ)).symm.map_eq

variable (n) in
/-- The lower-block chart in the coordinates `([g], x, u)`, `x ∈ ℝ^(n+1)`, `u ∈ ℝˣ`:
`([g], x, u) ↦ [[[g, 0], [x, u]]]`. -/
def lastRowChart (z : LeftUnipotentQuotient n ℝ × (Fin (n + 1) → ℝ) × ℝˣ) :
    LeftUnipotentQuotient (n + 1) ℝ :=
  lowerBlockQuotientChart (a := n + 1) (d := 1) (R := ℝ) (z.1, rowEquiv z.2.1, unitsLower z.2.2)

variable (n) in
/-- The measure `|det g|⁻¹ dD(g) dx |u|⁻¹ du` on the chart coordinates. -/
def lastRowMeasure (D : RealQuotientMeasureData n) :
    Measure (LeftUnipotentQuotient n ℝ × (Fin (n + 1) → ℝ) × ℝˣ) :=
  (D.measure.withDensity (quotientDensity n)).prod (volume.prod RealRankZero.unitsHaar)

theorem measurable_chart :
    Measurable (lowerBlockQuotientChart (a := n + 1) (d := 1) (R := ℝ)) := by
  have : SecondCountableTopology (LeftUnipotentQuotient n ℝ) :=
    (leftQuotient_isOpenQuotientMap _).secondCountableTopology
  have : SecondCountableTopology (Matrix (Fin 1) (Fin (n + 1)) ℝ) :=
    inferInstanceAs (SecondCountableTopology (Fin 1 → Fin (n + 1) → ℝ))
  have : SecondCountableTopology (lowerTriangularSubgroup 1 ℝ) :=
    IsEmbedding.subtypeVal.secondCountableTopology
  exact continuous_lowerBlockQuotientChart.measurable

theorem measurable_lastRowChart : Measurable (lastRowChart n) :=
  measurable_chart.comp
    (measurable_fst.prodMk ((rowEquiv.measurable.comp (measurable_fst.comp measurable_snd)).prodMk
      (measurable_unitsLower.comp (measurable_snd.comp measurable_snd))))

/-- **The last-row chart of a compatible real quotient measure.** -/
theorem exists_lastRowChart (D : RealQuotientMeasureData n) (D' : RealQuotientMeasureData (n + 1)) :
    ∃ C : ℝ, 0 < C ∧ D'.measure = ENNReal.ofReal C • (lastRowMeasure n D).map (lastRowChart n) := by
  obtain ⟨C, hC, hEq⟩ := chart_eq_smul_map D D' lowerHaar lowerHaar_ne_zero
  refine ⟨C, hC, ?_⟩
  rw [hEq]
  congr 1
  have he : Measurable (Prod.map (id : LeftUnipotentQuotient n ℝ → _)
      (Prod.map (rowEquiv (n := n)) unitsLower)) :=
    measurable_id.prodMap ((rowEquiv (n := n)).measurable.prodMap measurable_unitsLower)
  have hfun : lastRowChart n = lowerBlockQuotientChart ∘ Prod.map id (Prod.map rowEquiv unitsLower) :=
    rfl
  rw [hfun, lastRowMeasure, ← Measure.map_map measurable_chart he,
    ← map_prod_map _ _ measurable_id
      ((rowEquiv (n := n)).measurable.prodMap measurable_unitsLower),
    ← map_prod_map _ _ (rowEquiv (n := n)).measurable measurable_unitsLower, map_rowEquiv,
    Measure.map_id]
  rfl

/-- Integrability and integrals over `N_(n+2) \ GL_(n+2)(ℝ)` in last-row coordinates. -/
theorem lastRowChart_integral (D : RealQuotientMeasureData n)
    (D' : RealQuotientMeasureData (n + 1)) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : LeftUnipotentQuotient (n + 1) ℝ → ℂ, Measurable f →
      (Integrable f D'.measure ↔ Integrable (f ∘ lastRowChart n) (lastRowMeasure n D)) ∧
      ∫ q, f q ∂D'.measure = (C : ℂ) * ∫ z, f (lastRowChart n z) ∂lastRowMeasure n D := by
  obtain ⟨C, hC, hEq⟩ := exists_lastRowChart D D'
  refine ⟨C, hC, fun f hf => ⟨?_, ?_⟩⟩
  · rw [hEq, integrable_smul_measure (ENNReal.ofReal_pos.mpr hC).ne' ENNReal.ofReal_ne_top]
    exact integrable_map_measure hf.aestronglyMeasurable measurable_lastRowChart.aemeasurable
  · rw [hEq, integral_smul_measure, integral_map measurable_lastRowChart.aemeasurable
      hf.aestronglyMeasurable, ENNReal.toReal_ofReal hC.le, Complex.real_smul]

end Measures

end Langlands.Global.RankinSelbergGlobal.RealLowerBlockChart

namespace Langlands.Global.RankinSelbergGlobal

open RealLowerBlockChart ArchimedeanLocal MeasureTheory

attribute [local instance] archimedeanRealGLMeasurable archimedeanRealGLBorel
  archimedeanRealNMeasurable archimedeanRealNBorel archimedeanRealQMeasurable
  archimedeanRealQBorel RealRankZero.unitsMeasurable RealRankZero.unitsBorel

/-- **Last-row coordinates of real unipotent quotients.** For compatible quotient measure data
`D` on `N_(n+1) \ GL_(n+1)(ℝ)` and `D'` on `N_(n+2) \ GL_(n+2)(ℝ)`, there is `C > 0` such that
`D'` is `C` times the pushforward of `|det g|⁻¹ dD([g]) dx |u|⁻¹ du` (`x ∈ ℝ^(n+1)`, `u ∈ ℝˣ`)
along `([g], x, u) ↦ [[[g, 0], [x, u]]]`. -/
def RealLastRowChartStatement : Prop :=
  ∀ (n : ℕ) (D : RealQuotientMeasureData n) (D' : RealQuotientMeasureData (n + 1)),
    ∃ C : ℝ, 0 < C ∧ D'.measure = ENNReal.ofReal C • (lastRowMeasure n D).map (lastRowChart n)

theorem realLastRowChart : RealLastRowChartStatement :=
  fun _ D D' => exists_lastRowChart D D'

end Langlands.Global.RankinSelbergGlobal
