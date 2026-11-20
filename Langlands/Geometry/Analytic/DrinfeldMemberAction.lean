import Langlands.Geometry.Analytic.DrinfeldGroupAction
import Langlands.Geometry.Analytic.GeneralizedAffinoid.CoordinateContinuity
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalNormSectionContinuity
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.Group.Subgroup

/-! # Norm-continuous actions of member stabilizers on the chart algebras of `V_N` -/

noncomputable section

universe u v

namespace Langlands.Analytic.DrinfeldUpperHalfSpace

open Set Filter Topology PresentedAffinoidAlgebra GeneralizedTateAlgebra CategoryTheory
open AnalyticAffineSpace ExhaustionIndex

variable {F : Type v} [NontriviallyNormedField F] [ProperSpace F]
  (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [NormedAlgebra F K] {d : ℕ}

/-! ## Continuity of the coordinate images in the matrix -/

omit [ProperSpace F] [IsUltrametricDist K] [CompleteSpace K] in
theorem continuous_coefficients : Continuous (coefficients F K d) :=
  continuous_pi fun j => (continuous_algebraMap F K).comp (continuous_apply j)

omit [ProperSpace F] in
theorem continuous_entries_row (k : Fin (d + 1)) :
    Continuous (fun γ : Matrix.GeneralLinearGroup (Fin (d + 1)) F => entries γ k) :=
  continuous_pi fun j =>
    (Units.continuous_val (M := Matrix (Fin (d + 1)) (Fin (d + 1)) F)).matrix_elem k j

omit [ProperSpace F] in
theorem continuous_entries :
    Continuous (fun γ : Matrix.GeneralLinearGroup (Fin (d + 1)) F => entries γ) :=
  continuous_pi fun k => continuous_entries_row k

omit [CompleteSpace K] in
theorem continuous_linearForm (m : ℕ) :
    Continuous (fun c : Fin (d + 1) → K => linearForm K d m c) := by
  unfold linearForm
  exact ((continuous_algebraMap K (disc K d m)).comp (continuous_apply 0)).add
    (continuous_finsetSum _ fun i _ =>
      Continuous.smul (f := fun c : Fin (d + 1) → K => c i.succ)
        (g := fun _ => coordinate K (disc K d m) i) (continuous_apply _) continuous_const)

variable (F d) in
/-- The constructed inverse of `ℓ_c` on `V_N` is the ring inverse. -/
theorem inverse_eq_ringInverse {c : Fin (d + 1) → F} (hc : c ≠ 0) (N : ℕ) :
    inverse F K d hc N = Ring.inverse
      ((exhaustionChart F K d N).baseMap (linearForm K d N (coefficients F K d c))) := by
  have h := linearForm_mul_inverse F K d hc N
  have hu := IsUnit.of_mul_eq_one _ h
  calc inverse F K d hc N
      = (Ring.inverse ((exhaustionChart F K d N).baseMap
          (linearForm K d N (coefficients F K d c))) *
        (exhaustionChart F K d N).baseMap (linearForm K d N (coefficients F K d c))) *
          inverse F K d hc N := by rw [Ring.inverse_mul_cancel _ hu, one_mul]
    _ = Ring.inverse ((exhaustionChart F K d N).baseMap
          (linearForm K d N (coefficients F K d c))) := by rw [mul_assoc, h, mul_one]

omit [CompleteSpace K] in
/-- The image of `ℓ_{c(γ)}` in the chart algebra of `V_N` is continuous in `γ`
when the coefficient vector is. -/
theorem continuous_baseMap_linearForm {X : Type*} [TopologicalSpace X] (N : ℕ)
    {c : X → Fin (d + 1) → F} (hc : Continuous c) :
    Continuous (fun x => (exhaustionChart F K d N).baseMap
      (linearForm K d N (coefficients F K d (c x)))) :=
  (exhaustionChart F K d N).baseMap.continuous.comp
    ((continuous_linearForm K N).comp ((continuous_coefficients K).comp hc))

/-- The inverse of `ℓ_{γ_0}` on `V_N` is continuous in `γ`. -/
theorem continuous_inverse_entries (N : ℕ) :
    Continuous (fun γ : Matrix.GeneralLinearGroup (Fin (d + 1)) F =>
      inverse F K d (entries_row_zero_ne_zero γ) N) := by
  simp_rw [inverse_eq_ringInverse F K d]
  have hb := continuous_baseMap_linearForm K N (continuous_entries_row (F := F) (d := d) 0)
  refine continuous_iff_continuousAt.2 fun γ => ?_
  have hu := IsUnit.of_mul_eq_one _
    (linearForm_mul_inverse F K d (entries_row_zero_ne_zero γ) N)
  have h : ContinuousAt Ring.inverse ((exhaustionChart F K d N).baseMap
      (linearForm K d N (coefficients F K d (entries γ 0)))) :=
    hu.unit_spec ▸ NormedRing.inverse_continuousAt hu.unit
  exact ContinuousAt.comp (g := Ring.inverse)
    (f := fun γ : Matrix.GeneralLinearGroup (Fin (d + 1)) F => (exhaustionChart F K d N).baseMap
      (linearForm K d N (coefficients F K d (entries γ 0)))) h hb.continuousAt

/-- The coordinate images `ℓ_{γ_{i+1}} / ℓ_{γ_0}` are continuous in `γ`. -/
theorem continuous_actionTuple (N : ℕ) (i : Fin d) :
    Continuous (fun γ : Matrix.GeneralLinearGroup (Fin (d + 1)) F =>
      actionTuple K (entries γ) (entries_row_zero_ne_zero γ) N i) :=
  (continuous_baseMap_linearForm K N (continuous_entries_row i.succ)).mul
    (continuous_inverse_entries K N)

/-- The images `ℓ_{b γ} / ℓ_{γ_0}` are continuous in `γ`. -/
theorem continuous_linearForm_vecMul_mul_inverse (N : ℕ) (b : Fin (d + 1) → F) :
    Continuous (fun γ : Matrix.GeneralLinearGroup (Fin (d + 1)) F =>
      (exhaustionChart F K d N).baseMap
          (linearForm K d N (coefficients F K d (Matrix.vecMul b (entries γ)))) *
        inverse F K d (entries_row_zero_ne_zero γ) N) :=
  (continuous_baseMap_linearForm K N (continuous_const.matrix_vecMul continuous_entries)).mul
    (continuous_inverse_entries K N)

omit [ProperSpace F] [IsUltrametricDist K] [CompleteSpace K] in
theorem vecMul_entries_one (b : Fin (d + 1) → F) :
    Matrix.vecMul b (entries (1 : Matrix.GeneralLinearGroup (Fin (d + 1)) F)) = b := by
  change Matrix.vecMul b ((1 : Matrix.GeneralLinearGroup (Fin (d + 1)) F) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) F) = b
  rw [Matrix.GeneralLinearGroup.coe_one, Matrix.vecMul_one]

/-! ## A bounded evaluation out of the polydisc with small coordinate images -/

/-- Evaluation of the `N`-th polydisc algebra at a tuple of norm at most the radius. -/
def discEvaluation (N : ℕ) {B : PresentedAffinoidAlgebra K} (t : Fin d → B)
    (ht : ∀ i, ‖t i‖ ≤ radius K N) : BoundedAlgHom K (disc K d N) B := by
  letI := (disc K d N).ideal_closed
  exact BoundedAlgHom.liftQuotient K (disc K d N).ideal
    (evaluateHom (polyradius K d N) K _ t
      ⟨1, one_pos, fun e => by
        rw [one_mul]
        exact monomialValue_norm_le_weight _ _ (norm_one_le K _) _ ht e⟩)
    (by
      intro a ha
      have ha0 : a = 0 := ha
      rw [ha0, map_zero])

theorem discEvaluation_coordinate (N : ℕ) {B : PresentedAffinoidAlgebra K} (t : Fin d → B)
    (ht : ∀ i, ‖t i‖ ≤ radius K N) (i : Fin d) :
    discEvaluation K N t ht (coordinate K (disc K d N) i) = t i :=
  evaluate_X (polyradius K d N) K _ _ i

/-! ## Near the identity a matrix maps each member into itself -/

variable [NeZero d]

/-- If `γ` has a pullback from the member `V` to itself, it maps `V` into `V`. -/
theorem mapsTo_of_isActionPullback {γ : Matrix.GeneralLinearGroup (Fin (d + 1)) F}
    {V : ExhaustionIndex F K d}
    {φ : BoundedAlgHom K (exhaustionChart F K d V.level).algebra
      (exhaustionChart F K d V.level).algebra}
    (hφ : IsActionPullback K (entries γ) (entries_row_zero_ne_zero γ) V V φ)
    (z : Omega F K d) (hz : z.1 ∈ V.1) : (actionMap K γ z).1 ∈ V.1 := by
  have hz' : z ∈ range (exhaustionChartMap F K d V) := by
    rw [range_exhaustionChartMap]
    exact hz
  obtain ⟨x, rfl⟩ := hz'
  rw [actionMap_chart, ← hφ.chart_eq K x]
  exact mem_exhaustionChartMap K V _

omit [NeZero d] in
/-- For `γ` near the identity there is a pullback from `V` to itself. -/
theorem eventually_exists_isActionPullback (V : ExhaustionIndex F K d) :
    ∀ᶠ γ in 𝓝 (1 : Matrix.GeneralLinearGroup (Fin (d + 1)) F),
      ∃ φ : BoundedAlgHom K (exhaustionChart F K d V.level).algebra
          (exhaustionChart F K d V.level).algebra,
        IsActionPullback K (entries γ) (entries_row_zero_ne_zero γ) V V φ := by
  set N := V.level
  set A := (exhaustionChart F K d N).algebra
  have hcoord : ∀ᶠ γ in 𝓝 (1 : Matrix.GeneralLinearGroup (Fin (d + 1)) F), ∀ i,
      ‖actionTuple K (entries γ) (entries_row_zero_ne_zero γ) N i‖ ≤ polyradius K d N i := by
    apply eventually_coordinates_norm_le (polyradius K d N)
      (fun γ i => actionTuple K (entries γ) (entries_row_zero_ne_zero γ) N i)
      (fun i => (continuous_actionTuple K N i).continuousAt)
    intro i
    rw [actionTuple_one]
    exact (Langlands.Analytic.PresentedAffinoidAlgebra.RationalPresentation.norm_baseMap_le K (disc K d N) _ _ _ _).trans
      (norm_coordinate_le K (disc K d N) i)
  have hnet : ∀ᶠ γ in 𝓝 (1 : Matrix.GeneralLinearGroup (Fin (d + 1)) F), ∀ b ∈ net F K d N,
      ‖(exhaustionChart F K d N).baseMap
          (linearForm K d N (coefficients F K d (Matrix.vecMul b (entries γ)))) *
        inverse F K d (entries_row_zero_ne_zero γ) N -
        (exhaustionChart F K d N).baseMap (linearForm K d N (coefficients F K d b))‖ <
        threshold N := by
    apply (Finset.eventually_all (net F K d N)).2
    intro b _
    have h1 : (exhaustionChart F K d N).baseMap
          (linearForm K d N (coefficients F K d (Matrix.vecMul b
            (entries (1 : Matrix.GeneralLinearGroup (Fin (d + 1)) F))))) *
        inverse F K d (entries_row_zero_ne_zero 1) N =
        (exhaustionChart F K d N).baseMap (linearForm K d N (coefficients F K d b)) := by
      rw [vecMul_entries_one, inverse_one, mul_one]
    have hc := (continuous_linearForm_vecMul_mul_inverse K N b).tendsto' 1 _ h1
    filter_upwards [Metric.tendsto_nhds.mp hc (threshold N) (threshold_pos N)] with γ hγ
    rwa [dist_eq_norm] at hγ
  filter_upwards [hcoord, hnet] with γ hγc hγn
  let χ := discEvaluation K N (actionTuple K (entries γ) (entries_row_zero_ne_zero γ) N) hγc
  have hχ : ∀ i, χ (coordinate K (disc K d N) i) =
      actionTuple K (entries γ) (entries_row_zero_ne_zero γ) N i :=
    discEvaluation_coordinate K N _ hγc
  have himage : HasImageIn K χ (exhaustionChart F K d N).locus := by
    intro x
    have hx : BanachSpectrum.comap (exhaustionChart F K d N).baseMap.toBoundedRingHom x ∈
        (exhaustionChart F K d N).locus := by
      rw [← (RationalChart.represents (exhaustionChart F K d N)).2.1]
      exact mem_range_self x
    rw [mem_locus_exhaustionChart] at hx ⊢
    intro b hb
    have hval : χ (linearForm K d N (coefficients F K d b)) =
        (exhaustionChart F K d N).baseMap
          (linearForm K d N (coefficients F K d (Matrix.vecMul b (entries γ)))) *
          inverse F K d (entries_row_zero_ne_zero γ) N :=
      map_linearForm_of_coordinate K (entries γ) (entries_row_zero_ne_zero γ) N N χ hχ b
    have hlow := hx b hb
    change threshold N ≤ x (χ (linearForm K d N (coefficients F K d b)))
    rw [hval]
    set c := (exhaustionChart F K d N).baseMap (linearForm K d N (coefficients F K d b))
    set e := (exhaustionChart F K d N).baseMap
          (linearForm K d N (coefficients F K d (Matrix.vecMul b (entries γ)))) *
          inverse F K d (entries_row_zero_ne_zero γ) N
    have hlow' : threshold N ≤ x.toMulRingSeminorm c := hlow
    have hsmall : x.toMulRingSeminorm (e - c) < x.toMulRingSeminorm c :=
      ((x.le_norm _).trans_lt (hγn b hb)).trans_le hlow'
    have heq : x e = x c := by
      simpa only [sub_add_cancel] using
        (x.isNonarchimedean (K := K)).add_eq_right_of_lt
          (map_neg_eq_map x.toMulRingSeminorm) hsmall
    rw [heq]
    exact hlow'
  obtain ⟨φ, hφ, -⟩ := (RationalChart.represents (exhaustionChart F K d N)).2.2 A χ himage
  refine ⟨φ, fun i => ?_⟩
  have := congrArg (fun ψ : BoundedAlgHom K (disc K d N) A => ψ (coordinate K (disc K d N) i)) hφ
  exact this.trans (hχ i)

/-- For `γ` near the identity, `γ` maps the member `V` into itself. -/
theorem eventually_mapsTo (V : ExhaustionIndex F K d) :
    ∀ᶠ γ in 𝓝 (1 : Matrix.GeneralLinearGroup (Fin (d + 1)) F),
      ∀ z : Omega F K d, z.1 ∈ V.1 → (actionMap K γ z).1 ∈ V.1 := by
  filter_upwards [eventually_exists_isActionPullback K V] with γ ⟨φ, hφ⟩
  exact mapsTo_of_isActionPullback K hφ

/-! ## The stabilizer of a member -/

/-- The matrices preserving the member `V` of the exhaustion setwise. -/
def memberStabilizer (V : ExhaustionIndex F K d) :
    Subgroup (Matrix.GeneralLinearGroup (Fin (d + 1)) F) where
  carrier := {γ | ∀ z : Omega F K d, (actionMap K γ z).1 ∈ V.1 ↔ z.1 ∈ V.1}
  mul_mem' {a b} ha hb z := by
    rw [actionMap_mul K a b z, ha, hb]
  one_mem' z := by
    rw [actionMap_one K z]
  inv_mem' {a} ha z := by
    rw [← ha (actionMap K a⁻¹ z), ← actionMap_mul K a a⁻¹ z, mul_inv_cancel, actionMap_one K z]

theorem mem_memberStabilizer (V : ExhaustionIndex F K d)
    (γ : Matrix.GeneralLinearGroup (Fin (d + 1)) F) :
    γ ∈ memberStabilizer K V ↔ ∀ z : Omega F K d, (actionMap K γ z).1 ∈ V.1 ↔ z.1 ∈ V.1 :=
  Iff.rfl

theorem memberStabilizer_mem_nhds (V : ExhaustionIndex F K d) :
    (memberStabilizer K V : Set (Matrix.GeneralLinearGroup (Fin (d + 1)) F)) ∈
      𝓝 (1 : Matrix.GeneralLinearGroup (Fin (d + 1)) F) := by
  have hinv : Tendsto (fun γ : Matrix.GeneralLinearGroup (Fin (d + 1)) F => γ⁻¹)
      (𝓝 1) (𝓝 1) := by
    simpa only [inv_one] using (continuous_inv.tendsto (1 : Matrix.GeneralLinearGroup
      (Fin (d + 1)) F))
  filter_upwards [eventually_mapsTo K V, hinv.eventually (eventually_mapsTo K V)] with γ h1 h2
  intro z
  refine ⟨fun hz => ?_, h1 z⟩
  have h := h2 _ hz
  rwa [← actionMap_mul K γ⁻¹ γ z, inv_mul_cancel, actionMap_one K z] at h

theorem isOpen_memberStabilizer (V : ExhaustionIndex F K d) :
    IsOpen (memberStabilizer K V : Set (Matrix.GeneralLinearGroup (Fin (d + 1)) F)) :=
  Subgroup.isOpen_of_mem_nhds _ (memberStabilizer_mem_nhds K V)

/-! ## The pullback from a preserved member to itself -/

theorem targetIndex_subset_of_mem {V : ExhaustionIndex F K d}
    {γ : Matrix.GeneralLinearGroup (Fin (d + 1)) F} (hγ : γ ∈ memberStabilizer K V) :
    (targetIndex K γ V).1 ⊆ V.1 := by
  classical
  have hle : targetLevel K γ V ≤ V.level := by
    refine Nat.find_min' (exists_chartAction_subset K γ V) fun x => ?_
    rw [← actionMap_chart, V.exhaustion_level]
    exact (hγ _).2 (mem_exhaustionChartMap K V x)
  rw [← V.exhaustion_level]
  exact exhaustion_mono F K d hle

/-- The pullback along `γ` from a preserved member `V` to itself. -/
def selfPullback (V : ExhaustionIndex F K d) (γ : Matrix.GeneralLinearGroup (Fin (d + 1)) F)
    (hγ : γ ∈ memberStabilizer K V) :
    BoundedAlgHom K (exhaustionChart F K d V.level).algebra
      (exhaustionChart F K d V.level).algebra :=
  (pullback K γ V).comp (exhaustionRes K (targetIndex_subset_of_mem K hγ))

theorem selfPullback_isActionPullback (V : ExhaustionIndex F K d)
    (γ : Matrix.GeneralLinearGroup (Fin (d + 1)) F) (hγ : γ ∈ memberStabilizer K V) :
    IsActionPullback K (entries γ) (entries_row_zero_ne_zero γ) V V (selfPullback K V γ hγ) :=
  (pullback_isActionPullback K γ V).comp_res (targetIndex_subset_of_mem K hγ)

theorem selfPullback_eq_of_isActionPullback (V : ExhaustionIndex F K d)
    (γ : Matrix.GeneralLinearGroup (Fin (d + 1)) F) (hγ : γ ∈ memberStabilizer K V)
    {φ : BoundedAlgHom K (exhaustionChart F K d V.level).algebra
      (exhaustionChart F K d V.level).algebra}
    (hφ : IsActionPullback K (entries γ) (entries_row_zero_ne_zero γ) V V φ) :
    selfPullback K V γ hγ = φ :=
  (selfPullback_isActionPullback K V γ hγ).eq hφ

theorem selfPullback_congr (V : ExhaustionIndex F K d)
    {γ γ' : Matrix.GeneralLinearGroup (Fin (d + 1)) F} (e : γ = γ')
    (hγ : γ ∈ memberStabilizer K V) (hγ' : γ' ∈ memberStabilizer K V) :
    selfPullback K V γ hγ = selfPullback K V γ' hγ' := by
  subst e
  rfl

theorem selfPullback_comp (V : ExhaustionIndex F K d)
    (γ γ' : Matrix.GeneralLinearGroup (Fin (d + 1)) F) (hγ : γ ∈ memberStabilizer K V)
    (hγ' : γ' ∈ memberStabilizer K V) :
    (selfPullback K V γ' hγ').comp (selfPullback K V γ hγ) =
      selfPullback K V (γ * γ') ((memberStabilizer K V).mul_mem hγ hγ') :=
  (((selfPullback_isActionPullback K V γ' hγ').comp
    (selfPullback_isActionPullback K V γ hγ) (entries_row_zero_ne_zero (γ * γ'))
    (entries_mul γ γ')).eq (selfPullback_isActionPullback K V (γ * γ') _))

theorem selfPullback_one (V : ExhaustionIndex F K d) (h : (1 : Matrix.GeneralLinearGroup
    (Fin (d + 1)) F) ∈ memberStabilizer K V) :
    selfPullback K V 1 h = BoundedAlgHom.id K _ :=
  (selfPullback_isActionPullback K V 1 h).eq (isActionPullback_id K V)

/-- The chart point of `γ · x` is `γ` applied to the chart point of `x`. -/
theorem actionMap_exhaustionChartMap_selfPullback (V : ExhaustionIndex F K d)
    (γ : Matrix.GeneralLinearGroup (Fin (d + 1)) F) (hγ : γ ∈ memberStabilizer K V)
    (x : BanachSpectrum (exhaustionChart F K d V.level).algebra) :
    actionMap K γ (exhaustionChartMap F K d V x) =
      exhaustionChartMap F K d V
        (BanachSpectrum.comap (selfPullback K V γ hγ).toBoundedRingHom x) := by
  apply Subtype.ext
  rw [actionMap_chart, ← (selfPullback_isActionPullback K V γ hγ).chart_eq K x]

/-! ## The action on the chart algebra -/

/-- The automorphism of the chart algebra of `V` given by `γ`: its forward map is
the pullback along `γ⁻¹`, so that the assignment is a group homomorphism. -/
def memberAut (V : ExhaustionIndex F K d) (γ : memberStabilizer K V) :
    Aut ((exhaustionChart F K d V.level).algebra) where
  hom := selfPullback K V (γ⁻¹ : memberStabilizer K V).1 (γ⁻¹).2
  inv := selfPullback K V γ.1 γ.2
  hom_inv_id := by
    change (selfPullback K V γ.1 γ.2).comp (selfPullback K V (γ⁻¹ : memberStabilizer K V).1
      (γ⁻¹).2) = BoundedAlgHom.id K _
    rw [selfPullback_comp]
    rw [selfPullback_congr K V (show (γ⁻¹ : memberStabilizer K V).1 * γ.1 = 1 by
      rw [Subgroup.coe_inv, inv_mul_cancel]) _ (memberStabilizer K V).one_mem]
    exact selfPullback_one K V _
  inv_hom_id := by
    change (selfPullback K V (γ⁻¹ : memberStabilizer K V).1 (γ⁻¹).2).comp
      (selfPullback K V γ.1 γ.2) = BoundedAlgHom.id K _
    rw [selfPullback_comp]
    rw [selfPullback_congr K V (show γ.1 * (γ⁻¹ : memberStabilizer K V).1 = 1 by
      rw [Subgroup.coe_inv, mul_inv_cancel]) _ (memberStabilizer K V).one_mem]
    exact selfPullback_one K V _

theorem memberAut_hom (V : ExhaustionIndex F K d) (γ : memberStabilizer K V) :
    (memberAut K V γ).hom = selfPullback K V (γ⁻¹ : memberStabilizer K V).1 (γ⁻¹).2 := rfl

theorem memberAut_inv (V : ExhaustionIndex F K d) (γ : memberStabilizer K V) :
    (memberAut K V γ).inv = selfPullback K V γ.1 γ.2 := rfl

/-- The action of the stabilizer of `V` on the chart algebra of `V`. -/
def memberAction (V : ExhaustionIndex F K d) :
    memberStabilizer K V →* Aut ((exhaustionChart F K d V.level).algebra) where
  toFun := memberAut K V
  map_one' := by
    apply Iso.ext
    change selfPullback K V ((1 : memberStabilizer K V)⁻¹).1 ((1 : memberStabilizer K V)⁻¹).2 =
      BoundedAlgHom.id K _
    rw [selfPullback_congr K V (show ((1 : memberStabilizer K V)⁻¹).1 = 1 by simp)
      _ (memberStabilizer K V).one_mem]
    exact selfPullback_one K V _
  map_mul' γ γ' := by
    apply Iso.ext
    change selfPullback K V ((γ * γ')⁻¹ : memberStabilizer K V).1 ((γ * γ')⁻¹).2 =
      (selfPullback K V (γ⁻¹ : memberStabilizer K V).1 (γ⁻¹).2).comp
        (selfPullback K V (γ'⁻¹ : memberStabilizer K V).1 (γ'⁻¹).2)
    rw [selfPullback_comp]
    exact selfPullback_congr K V (by simp [mul_inv_rev]) _ _

theorem memberAction_hom (V : ExhaustionIndex F K d) (γ : memberStabilizer K V) :
    (memberAction K V γ).hom = selfPullback K V (γ⁻¹ : memberStabilizer K V).1 (γ⁻¹).2 := rfl

theorem memberAction_inv (V : ExhaustionIndex F K d) (γ : memberStabilizer K V) :
    (memberAction K V γ).inv = selfPullback K V γ.1 γ.2 := rfl

/-! ## Norm continuity of the orbits -/

omit [CompleteSpace K] in
theorem aut_mul_hom {A : PresentedAffinoidAlgebra K} (a b : Aut A) :
    (a * b).hom = a.hom.comp b.hom := rfl

omit [CompleteSpace K] in
theorem aut_one_hom_apply {A : PresentedAffinoidAlgebra K} (x : A) :
    (1 : Aut A).hom.toAlgHom x = x := rfl

omit [CompleteSpace K] [NeZero d] in
theorem norm_baseMap_coordinate_le (N : ℕ) (i : Fin d) :
    ‖(exhaustionChart F K d N).baseMap (coordinate K (disc K d N) i)‖ ≤ polyradius K d N i :=
  (Langlands.Analytic.PresentedAffinoidAlgebra.RationalPresentation.norm_baseMap_le K
    (disc K d N) _ _ _ _).trans (norm_coordinate_le K (disc K d N) i)

omit [ProperSpace F] [IsUltrametricDist K] [CompleteSpace K] [NeZero d] in
theorem continuous_val_inv (H : Subgroup (Matrix.GeneralLinearGroup (Fin (d + 1)) F)) :
    Continuous (fun γ : H => ((γ⁻¹ : H) : Matrix.GeneralLinearGroup (Fin (d + 1)) F)) :=
  continuous_subtype_val.comp continuous_inv

theorem continuousAt_memberAction_baseMap (V : ExhaustionIndex F K d) (a : disc K d V.level) :
    ContinuousAt (fun γ : memberStabilizer K V =>
      (memberAction K V γ).hom.toAlgHom ((exhaustionChart F K d V.level).baseMap a)) 1 := by
  let φ : memberStabilizer K V → BoundedAlgHom K (disc K d V.level)
      (exhaustionChart F K d V.level).algebra :=
    fun γ => ((memberAction K V γ).hom).comp (exhaustionChart F K d V.level).baseMap
  change ContinuousAt (fun γ => φ γ a) 1
  apply continuousAt_map_of_coordinates φ
  · intro i
    have heq : (fun γ => φ γ (coordinate K (disc K d V.level) i)) =
        (fun γ : memberStabilizer K V => actionTuple K (entries (γ⁻¹ : memberStabilizer K V).1)
          (entries_row_zero_ne_zero _) V.level i) := by
      funext γ
      show (memberAction K V γ).hom.toAlgHom ((exhaustionChart F K d V.level).baseMap
        (coordinate K (disc K d V.level) i)) = _
      rw [memberAction_hom]
      exact selfPullback_isActionPullback K V (γ⁻¹ : memberStabilizer K V).1 (γ⁻¹).2 i
    rw [heq]
    exact ((continuous_actionTuple K V.level i).comp
      (continuous_val_inv (memberStabilizer K V))).continuousAt
  · intro i
    change ‖(memberAction K V 1).hom.toAlgHom ((exhaustionChart F K d V.level).baseMap
      (coordinate K (disc K d V.level) i))‖ ≤ _
    rw [map_one, aut_one_hom_apply]
    exact norm_baseMap_coordinate_le K V.level i

/-- Every forward orbit of the action on the chart algebra of `V` is continuous in
the quotient norm. -/
theorem continuous_memberAction (V : ExhaustionIndex F K d)
    (a : (exhaustionChart F K d V.level).algebra) :
    Continuous (fun γ : memberStabilizer K V => (memberAction K V γ).hom.toAlgHom a) := by
  have hm (g h : memberStabilizer K V) :
      (memberAction K V (g * h)).hom = ((memberAction K V g).hom).comp
        (memberAction K V h).hom := by
    rw [map_mul, aut_mul_hom]
  apply continuous_map_of_continuousAt_one (fun g => (memberAction K V g).hom) hm
  intro b
  apply continuousAt_map_of_coordinates (fun g => (memberAction K V g).hom)
  · intro i
    exact (exhaustionChart F K d V.level).continuousAt_map_coordinates
      (fun g => (memberAction K V g).hom) (continuousAt_memberAction_baseMap K V) i
  · intro i
    show ‖(memberAction K V 1).hom.toAlgHom (coordinate K _ i)‖ ≤ _
    rw [map_one, aut_one_hom_apply]
    exact norm_coordinate_le K _ i

end Langlands.Analytic.DrinfeldUpperHalfSpace
