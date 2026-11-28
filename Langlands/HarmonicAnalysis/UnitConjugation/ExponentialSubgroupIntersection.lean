import Langlands.HarmonicAnalysis.UnitConjugation.ExponentialConjugacy
import Langlands.HarmonicAnalysis.UnitConjugation.ExponentialCongruenceHaar

/-! # Exponential coordinates on intersections of congruence subgroups -/

noncomputable section

namespace Langlands.HarmonicAnalysis.UnitConjugation

open Function MeasureTheory MeasureTheory.Measure Metric Set _root_.Topology

local notation "L(" A "," h ")" => OpenAddSubgroup.toAddSubgroup
  (IsUltrametricDist.closedBall_openAddSubgroup A h)
local notation "K(" A "," h "," h' ")" => normUnitCongruence (R := A) (le_of_lt h) h'

/-- The intersection with the pullback of a unit congruence subgroup is parametrized
by the corresponding additive lattice intersection. The exponential sends negatives
to inverses and preserves the indicated Haar measures. -/
def ExponentialSubgroupIntersectionStatement (F A B : Type*) [NontriviallyNormedField F]
    [IsUltrametricDist F] [CharZero F] [ProperSpace F]
    [NormedRing A] [NormedAlgebra F A] [IsUltrametricDist A] [ProperSpace A] [FiniteDimensional F A]
    [NormedRing B] [NormedAlgebra F B] [IsUltrametricDist B] [ProperSpace B] [FiniteDimensional F B]
    [MeasurableSpace A] [BorelSpace A] [MeasurableSpace Aˣ] [BorelSpace Aˣ]
    [MeasurableSpace B] [BorelSpace B] [MeasurableSpace Bˣ] [BorelSpace Bˣ] : Prop :=
  ∃ εA > (0 : ℝ), ∃ εB > (0 : ℝ),
    closedBall (0 : A) εA ⊆ eball 0 (NormedSpace.expSeries F A).radius ∧
    closedBall (0 : B) εB ⊆ eball 0 (NormedSpace.expSeries F B).radius ∧
    ∀ (r : ℝ) (hr : 0 < r) (hr₁ : r < 1) (s : ℝ) (hs : 0 < s) (hs₁ : s < 1),
      r ≤ εA → s ≤ εB → ∀ i : A →ₐ[F] B,
      (∀ x ∈ L(A, hr), ∃ e : B ≃ₐ[F] B,
        ∃ y ∈ eball 0 (NormedSpace.expSeries F B).radius, e y = i x) →
      let K := K(A, hr, hr₁)
      let J := K(B, hs, hs₁).comap ((Units.map i.toMonoidHom).comp K.subtype)
      let Q := L(B, hs).comap i.toAddMonoidHom ⊓ L(A, hr)
      ∃ E : Q ≃ₜ J, (∀ x, ((E x).val.val : A) = NormedSpace.exp (x : A) ∧
          (Units.map i.toMonoidHom (E x).val.val : B) = NormedSpace.exp (i (x : A))) ∧
        (∀ x, E (-x) = (E x)⁻¹) ∧ IsOpen (J : Set K) ∧ IsCompact (J : Set K) ∧
        ∀ (μ : Measure A) [μ.IsAddHaarMeasure],
          let ν := (μ.comap (normUnitCoordinate hr.le hr₁)).comap (Subtype.val : J → K)
          ν.IsHaarMeasure ∧ MeasurePreserving E (μ.comap Subtype.val) ν

variable {F A B : Type*} [NontriviallyNormedField F] [IsUltrametricDist F] [CharZero F]
  [ProperSpace F]
  [NormedRing A] [NormedAlgebra F A] [IsUltrametricDist A] [ProperSpace A] [FiniteDimensional F A]
  [NormedRing B] [NormedAlgebra F B] [IsUltrametricDist B] [ProperSpace B] [FiniteDimensional F B]
  [MeasurableSpace A] [BorelSpace A] [MeasurableSpace Aˣ] [BorelSpace Aˣ]
  [MeasurableSpace B] [BorelSpace B] [MeasurableSpace Bˣ] [BorelSpace Bˣ]

omit [ProperSpace F] in
private theorem exists_small_exp_radius (C : Type*) [NormedRing C] [NormedAlgebra F C]
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > (0 : ℝ), δ ≤ ε ∧ closedBall (0 : C) δ ⊆ eball 0 (NormedSpace.expSeries F C).radius := by
  have h := isOpen_eball.mem_nhds (mem_eball_self (x := (0 : C)) (exponentialPositiveRadius F C))
  obtain ⟨d, hd, hdsub⟩ := Metric.mem_nhds_iff.mp h
  let δ := min d ε / 2
  have hδε : δ ≤ ε := (half_lt_self (lt_min hd hε)).le.trans (min_le_right _ _)
  have hδd : δ < d := (half_lt_self (lt_min hd hε)).trans_le (min_le_left _ _)
  exact ⟨δ, half_pos (lt_min hd hε), hδε, (closedBall_subset_ball hδd).trans hdsub⟩

theorem exponentialSubgroupIntersection : ExponentialSubgroupIntersectionStatement F A B := by
  obtain ⟨dA, hdA, hChartA⟩ := exponentialCongruenceHaar (F := F) (A := A)
  obtain ⟨dB, hdB, hChartB⟩ := exponentialCongruenceHaar (F := F) (A := B)
  obtain ⟨εA, hεA, hAε, hAconv⟩ := exists_small_exp_radius (F := F) A dA hdA
  obtain ⟨εB, hεB, hBε, hBconv⟩ := exists_small_exp_radius (F := F) B dB hdB
  refine ⟨εA, hεA, εB, hεB, hAconv, hBconv, fun r hr hr₁ s hs hs₁ hAr hBs i hiSat => ?_⟩
  obtain ⟨chartA, hChartA, hAHaar⟩ := hChartA r hr hr₁ (hAr.trans hAε)
  obtain ⟨chartB, hChartB, _⟩ := hChartB s hs hs₁ (hBs.trans hBε)
  let LA := L(A, hr)
  let LB := L(B, hs)
  let KA := K(A, hr, hr₁)
  let KB := K(B, hs, hs₁)
  let EA : LA ≃ₜ KA := chartA
  let EB : LB ≃ₜ KB := chartB
  have hEA (x : LA) : ((EA x).val : A) = NormedSpace.exp (x : A) := hChartA x
  have hEB (x : LB) : ((EB x).val : B) = NormedSpace.exp (x : B) := hChartB x
  let φ := (Units.map i.toMonoidHom).comp KA.subtype
  let J := KB.comap φ
  let Q := LB.comap i.toAddMonoidHom ⊓ LA
  let j : Q → LA := fun x => ⟨x.val, x.property.2⟩
  let k : J → KA := Subtype.val
  have hi : Continuous i := i.toLinearMap.continuous_of_finiteDimensional
  have hφ : Continuous φ := (hi.units_map i.toMonoidHom).comp continuous_subtype_val
  have hJ : IsOpen (J : Set KA) := (isOpen_normUnitCongruence hs hs₁).preimage hφ
  let : CompactSpace KA := isCompact_iff_compactSpace.mp (isCompact_normUnitCongruence hr.le hr₁)
  have hJc : IsCompact (J : Set KA) := (J.isClosed_of_isOpen hJ).isCompact
  have hA (x : LA) : (x : A) ∈ eball 0 (NormedSpace.expSeries F A).radius :=
    hAconv (closedBall_subset_closedBall hAr x.property)
  have hB (y : LB) : (y : B) ∈ eball 0 (NormedSpace.expSeries F B).radius :=
    hBconv (closedBall_subset_closedBall hBs y.property)
  have hMap (x : LA) : i (NormedSpace.exp (x : A)) = NormedSpace.exp (i (x : A)) :=
    NormedSpace.map_exp_of_mem_ball i hi x (hA x)
  have hVal (x : LA) : (φ (EA x) : B) = NormedSpace.exp (i (x : A)) := by
    change i ((EA x).val : A) = _
    rw [hEA, hMap]
  have hMatch (x : LA) : i x.val ∈ LB ↔ EA x ∈ J := by
    constructor
    · intro hx
      let y : LB := ⟨i x.val, hx⟩
      have hEq : (EB y).val = φ (EA x) := Units.ext ((hEB y).trans (hVal x).symm)
      change φ (EA x) ∈ KB
      rw [← hEq]
      exact (EB y).property
    · intro hx
      let g : KB := ⟨φ (EA x), hx⟩
      let y : LB := EB.symm g
      have hEq : NormedSpace.exp (i x.val) = NormedSpace.exp (y : B) := by
        rw [← hVal x, ← hEB y]
        exact congrArg (fun u : KB => (u.val : B)) (EB.apply_symm_apply g).symm
      have hxy := exponentialConjugacy (F := F) (A := B) (hiSat x x.property)
        ⟨AlgEquiv.refl, y, hB y, rfl⟩ hEq
      exact hxy ▸ y.property
  let E : Q ≃ₜ J :=
    { toFun := fun x => ⟨EA (j x), (hMatch (j x)).mp x.property.1⟩
      invFun := fun z =>
        let x := EA.symm z.val
        have hzx : EA x ∈ J := (EA.apply_symm_apply z.val).symm ▸ z.property
        ⟨x.val, (hMatch x).mpr hzx, x.property⟩
      left_inv := fun x => Subtype.ext (congrArg (fun w : LA => (w : A)) (EA.symm_apply_apply (j x)))
      right_inv := fun z => Subtype.ext (EA.apply_symm_apply z.val)
      continuous_toFun := (EA.continuous.comp (continuous_subtype_val.subtype_mk _)).subtype_mk _
      continuous_invFun :=
        ((continuous_subtype_val.comp EA.symm.continuous).comp continuous_subtype_val).subtype_mk _ }
  have hEE (x : Q) : ((E x).val.val : A) = NormedSpace.exp (x : A) := hEA (j x)
  refine ⟨E, fun x => ⟨hEE x, hVal (j x)⟩, ?_, hJ, hJc, ?_⟩
  · intro x
    apply eq_inv_of_mul_eq_one_right
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    change ((E x).val.val : A) * ((E (-x)).val.val : A) = 1
    rw [hEE, hEE, AddSubgroup.coe_neg,
      ← NormedSpace.exp_add_of_commute_of_mem_ball (Commute.neg_right (Commute.refl _))
        (hA (j x)) (hA (j (-x))), add_neg_cancel, NormedSpace.exp_zero]
  intro μ _
  obtain ⟨hν, hPresA⟩ := hAHaar μ
  let ν := μ.comap (normUnitCoordinate hr.le hr₁)
  have hPres : MeasurePreserving EA (μ.comap (Subtype.val : LA → A)) ν := hPresA
  let : ν.IsHaarMeasure := hν
  have hk : IsOpenEmbedding k := hJ.isOpenEmbedding_subtypeVal
  have hLA : IsOpen (LA : Set A) := IsUltrametricDist.isOpen_closedBall _ hr.ne'
  have hLB : IsOpen (LB : Set B) := IsUltrametricDist.isOpen_closedBall _ hs.ne'
  have hj : IsOpenEmbedding j :=
    .of_comp j hLA.isOpenEmbedding_subtypeVal ((hLB.preimage hi).inter hLA).isOpenEmbedding_subtypeVal
  change (ν.comap k).IsHaarMeasure ∧ MeasurePreserving E (μ.comap Subtype.val) (ν.comap k)
  refine ⟨IsHaarMeasure.comap (mH := inferInstance) (f := J.subtype) ν hk,
    ⟨E.continuous.measurable, ?_⟩⟩
  have hComap : μ.comap (Subtype.val : Q → A) = (μ.comap (Subtype.val : LA → A)).comap j := by
    rw [comap_comap (fun _ h => hj.measurableEmbedding.measurableSet_image.mpr h)
      Subtype.val_injective
      (fun _ h => hLA.isOpenEmbedding_subtypeVal.measurableEmbedding.measurableSet_image.mpr h)]
    rfl
  rw [hComap]
  ext S hS
  rw [Measure.map_apply E.continuous.measurable hS,
    comap_apply j hj.injective (fun _ h => hj.measurableEmbedding.measurableSet_image.mpr h) _
      (E.continuous.measurable hS),
    comap_apply k hk.injective (fun _ h => hk.measurableEmbedding.measurableSet_image.mpr h) _ hS,
    ← hPres.map_eq,
    Measure.map_apply hPres.measurable (hk.measurableEmbedding.measurableSet_image.mpr hS)]
  congr 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨E y, hy, rfl⟩
  · rintro ⟨z, hz, hEq⟩
    let y := E.symm z
    have hEy : E y = z := E.apply_symm_apply z
    refine ⟨y, ?_, EA.injective ?_⟩
    · change E y ∈ S
      rwa [hEy]
    · change k (E y) = EA x
      rwa [hEy]

end Langlands.HarmonicAnalysis.UnitConjugation
