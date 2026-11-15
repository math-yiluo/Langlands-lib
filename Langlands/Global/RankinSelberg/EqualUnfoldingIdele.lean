import Langlands.Global.RankinSelberg.EqualIntegrals
import Langlands.Global.RankinSelberg.UnfoldingGL
import Langlands.Automorphic.RankOneDeterminantBand

/-! # The idele slab measure of the equal-rank Rankin–Selberg integral

For the Haar measure on `GL_1(𝔸) = 𝔸^×`: the commutativity of `GL_1(𝔸)`, the right and
inversion invariance of Haar measure, `0 < ideleSlabVolume F < ∞`, the independence of the
slab volume `F^× \ {c ≤ |a| < e c}` of `c`, and fiber mass one: every fundamental domain `D`
of `F^×` in `𝔸^×` satisfies `d^×a (D ∩ {c ≤ |a| < e c}) = 1` and
`d^×a (D ∩ {c < |a| ≤ e c}) = 1` for `d^×a = ideleMeasure F`. See the paired Markdown.
-/

noncomputable section
universe u
open NumberField MeasureTheory
open scoped CategoryTheory.MonObj
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

local instance ideleSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance ideleSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

variable (F : Type u) [Field F] [NumberField F]

section Points

/-- `GL_1(𝔸)` is commutative: a `1 × 1` matrix is the scalar matrix of its determinant. -/
theorem points_one_mul_comm (x y : Points F 1) : x * y = y * x := by
  apply (GeneralLinearGroupPoints.adelicEquiv F 1).injective
  rw [map_mul, map_mul,
    ← AdelicGL.scalar_determinant_one F (GeneralLinearGroupPoints.adelicEquiv F 1 x)]
  exact AdelicGL.scalar_commute F 1 _ _

/-- Haar measure on `GL_1(𝔸)` is right invariant. -/
instance isMulRightInvariant_haar_points_one :
    (Measure.haar : Measure (Points F 1)).IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  have h : (fun x : Points F 1 => x * g) = fun x => g * x :=
    funext fun x => points_one_mul_comm F x g
  rw [h]
  exact map_mul_left_eq_self _ g

/-- Haar measure on `GL_1(𝔸)` is invariant under inversion. -/
instance isInvInvariant_haar_points_one :
    (Measure.haar : Measure (Points F 1)).IsInvInvariant := by
  let _ : CommGroup (Points F 1) :=
    { (inferInstance : Group (Points F 1)) with mul_comm := points_one_mul_comm F }
  exact Measure.IsHaarMeasure.isInvInvariant_of_regular _

/-- The determinant norm of an inverse. -/
theorem detNorm_inv (n : ℕ) (x : Points F n) : detNorm F n x⁻¹ = (detNorm F n x)⁻¹ := by
  have h := Unfolding.detNorm_mul F n x⁻¹ x
  rw [inv_mul_cancel] at h
  have h1 : detNorm F n 1 = 1 := by
    simp only [detNorm, map_one, Units.val_one, NNReal.coe_one]
  rw [h1] at h
  exact eq_inv_of_mul_eq_one_left h.symm

/-- The determinant norm is invariant under left multiplication by `GL_n(F)`. -/
theorem detNorm_rationalSubgroup_mul (n : ℕ) {k : Points F n}
    (hk : k ∈ AdelicGroupPoints.rationalSubgroup F (Scheme F n)) (x : Points F n) :
    detNorm F n (k * x) = detNorm F n x := by
  rw [Unfolding.detNorm_mul, Unfolding.detNorm_of_mem_rationalSubgroup F n hk, one_mul]

/-- Every positive real number is the norm `|a|` of an idele `a ∈ GL_1(𝔸)`. -/
theorem exists_detNorm_eq {c : ℝ} (hc : 0 < c) : ∃ z : Points F 1, detNorm F 1 z = c := by
  let h : NNReal ˣ := Units.mk0 ⟨c, hc.le⟩ (by
    intro h0
    exact hc.ne' (congrArg (fun x : NNReal => (x : ℝ)) h0))
  refine ⟨(GeneralLinearGroupPoints.adelicEquiv F 1).symm
    (AdelicGL.scalar F 1 (IdeleAbsoluteValue.normSection F h)), ?_⟩
  simp only [detNorm, MulEquiv.apply_symm_apply,
    AdelicBlockDeterminantCharacter.determinantNorm_scalar,
    IdeleAbsoluteValue.full_normSection, pow_one]
  rfl

end Points

section Slab

/-- Membership of a class in the slab only depends on the norm of any representative. -/
theorem mk_mem_determinantSlab_iff (n : ℕ) (a b : ℝ) (g : Points F n) :
    LeftCosetSpace.mk (AdelicGroupPoints.rationalSubgroup F (Scheme F n)) g ∈
        determinantSlab F n a b ↔
      a ≤ detNorm F n g ∧ detNorm F n g < b := by
  constructor
  · rintro ⟨g', hg', hgg'⟩
    have hmem := (LeftCosetSpace.mk_eq_mk_iff _ g' g).mp hgg'
    have hnorm : detNorm F n g = detNorm F n g' := by
      rw [← detNorm_rationalSubgroup_mul F n hmem g', inv_mul_cancel_right]
    rw [hnorm]
    exact hg'
  · intro hg
    exact ⟨g, hg, rfl⟩

/-- The preimage of the slab in `GL_n(𝔸)`. -/
theorem preimage_mk_determinantSlab (n : ℕ) (a b : ℝ) :
    LeftCosetSpace.mk (AdelicGroupPoints.rationalSubgroup F (Scheme F n)) ⁻¹'
        determinantSlab F n a b =
      {g : Points F n | a ≤ detNorm F n g ∧ detNorm F n g < b} := by
  ext g
  exact mk_mem_determinantSlab_iff F n a b g

/-- The set of points with `a ≤ |det g| < b` is measurable. -/
theorem measurableSet_detNorm_Ico (n : ℕ) (a b : ℝ) :
    MeasurableSet {g : Points F n | a ≤ detNorm F n g ∧ detNorm F n g < b} :=
  (measurableSet_le measurable_const (Unfolding.continuous_detNorm F n).measurable).inter
    (measurableSet_lt (Unfolding.continuous_detNorm F n).measurable measurable_const)

/-- The slab is a measurable set of `GL_n(F) \ GL_n(𝔸)`. -/
theorem measurableSet_determinantSlab (n : ℕ) (a b : ℝ) :
    MeasurableSet (determinantSlab F n a b) := by
  rw [measurableSet_quotient, Quotient.mk''_eq_mk]
  change MeasurableSet (LeftCosetSpace.mk (AdelicGroupPoints.rationalSubgroup F (Scheme F n)) ⁻¹'
    determinantSlab F n a b)
  rw [preimage_mk_determinantSlab]
  exact measurableSet_detNorm_Ico F n a b

/-- The slab volume, computed on any fundamental domain of `GL_n(F)` in `GL_n(𝔸)`. -/
theorem rationalQuotientHaarMeasure_determinantSlab_eq (n : ℕ) {D : Set (Points F n)}
    (hD : IsFundamentalDomain (AdelicGroupPoints.rationalSubgroup F (Scheme F n)) D
      Measure.haar) (a b : ℝ) :
    AdelicGroupPoints.rationalQuotientHaarMeasure F (Scheme F n) (determinantSlab F n a b) =
      Measure.haar (D ∩ {g : Points F n | a ≤ detNorm F n g ∧ detNorm F n g < b}) := by
  rw [AdelicGroupPoints.rationalQuotientHaarMeasure_eq F _ hD,
    LeftCosetSpace.quotientMeasure_apply _ _ _ (measurableSet_determinantSlab F n a b),
    preimage_mk_determinantSlab, Set.inter_comm]

/-- Right translation by `t` carries the slab `a ≤ |g| < b` to `a |t| ≤ |g| < b |t|`, and
preserves the quotient measure. -/
theorem rationalQuotientHaarMeasure_determinantSlab_mul (a b : ℝ) (t : Points F 1) :
    AdelicGroupPoints.rationalQuotientHaarMeasure F (Scheme F 1)
        (determinantSlab F 1 (a * detNorm F 1 t) (b * detNorm F 1 t)) =
      AdelicGroupPoints.rationalQuotientHaarMeasure F (Scheme F 1) (determinantSlab F 1 a b) := by
  have hmp := AdelicGroupPoints.measurePreserving_rightTranslate_rationalQuotientHaarMeasure
    F (Scheme F 1) t
  have hpre : LeftCosetSpace.rightTranslate _ t ⁻¹'
      determinantSlab F 1 (a * detNorm F 1 t) (b * detNorm F 1 t) =
        determinantSlab F 1 a b := by
    ext q
    obtain ⟨g, rfl⟩ := LeftCosetSpace.mk_surjective _ q
    have ht := Unfolding.detNorm_pos F 1 t
    simp only [Set.mem_preimage, LeftCosetSpace.rightTranslate_mk, mk_mem_determinantSlab_iff,
      Unfolding.detNorm_mul]
    rw [mul_le_mul_iff_of_pos_right ht, mul_lt_mul_iff_of_pos_right ht]
  rw [← hpre, hmp.measure_preimage (measurableSet_determinantSlab F 1 _ _).nullMeasurableSet]

/-- The slab `F^× \ {c ≤ |a| < e c}` has the volume of `F^× \ {1 ≤ |a| < e}` for every `c > 0`. -/
theorem rationalQuotientHaarMeasure_determinantSlab {c : ℝ} (hc : 0 < c) :
    AdelicGroupPoints.rationalQuotientHaarMeasure F (Scheme F 1)
        (determinantSlab F 1 c (Real.exp 1 * c)) = ideleSlabVolume F := by
  obtain ⟨t, ht⟩ := exists_detNorm_eq F hc
  have h := rationalQuotientHaarMeasure_determinantSlab_mul F 1 (Real.exp 1) t
  rw [ht, one_mul] at h
  exact h

end Slab

section Volume

/-- The idele slab volume is finite: a compact set of ideles meets every class of the slab. -/
theorem ideleSlabVolume_ne_top : ideleSlabVolume F ≠ ⊤ := by
  obtain ⟨K, hK, hcover⟩ :=
    AdelicGL.exists_isCompact_determinantBandCover F 1 (Real.exp 1) one_pos
  let e := GeneralLinearGroupPoints.adelicHomeomorph F 1
  have hK' : IsCompact (e ⁻¹' K) := e.toHomeomorph.isCompact_preimage.mpr hK
  have hsub : determinantSlab F 1 1 (Real.exp 1) ⊆
      LeftCosetSpace.mk (AdelicGroupPoints.rationalSubgroup F (Scheme F 1)) '' (e ⁻¹' K) := by
    rintro _ ⟨g, ⟨h1, h2⟩, rfl⟩
    obtain ⟨a, ha⟩ := hcover (e g) ⟨h1, h2.le⟩
    refine ⟨rationalPoint F 1 a * g, ?_, ?_⟩
    · change e (rationalPoint F 1 a * g) ∈ K
      rw [map_mul]
      have hr : e (rationalPoint F 1 a) = AdelicGL.rational F 1 a := by
        change GeneralLinearGroupPoints.adelicEquiv F 1 (AdelicGroupPoints.rational F
          (Scheme F 1) ((GeneralLinearGroupPoints.rationalEquiv F 1).symm a)) = _
        rw [GeneralLinearGroupPoints.adelicEquiv_rational, MulEquiv.apply_symm_apply]
      rw [hr]
      exact ha
    · exact LeftCosetSpace.mk_subgroup_mul _
        ⟨rationalPoint F 1 a, MonoidHom.mem_range.mpr ⟨_, rfl⟩⟩ g
  exact ne_top_of_le_ne_top
    (hK'.image (LeftCosetSpace.continuous_mk _)).measure_lt_top.ne (measure_mono hsub)

/-- The idele slab volume is nonzero: the slab contains the image of a nonempty open set. -/
theorem ideleSlabVolume_ne_zero : ideleSlabVolume F ≠ 0 := by
  set Γ := AdelicGroupPoints.rationalSubgroup F (Scheme F 1)
  have hΓ := AdelicGroupPoints.isDiscrete_rationalSubgroup F (Scheme F 1)
  set S : Set (Points F 1) := {g | 1 ≤ detNorm F 1 g ∧ detNorm F 1 g < Real.exp 1}
  have hD := LeftCosetSpace.isFundamentalDomain Γ hΓ (Measure.haar : Measure (Points F 1))
  intro h0
  have hS0 : (Measure.haar : Measure (Points F 1)) S = 0 := by
    refine hD.measure_zero_of_invariant S (fun k => ?_) ?_
    · ext x
      rw [Set.mem_smul_set_iff_inv_smul_mem]
      change (1 ≤ detNorm F 1 ((k⁻¹ : Γ) * x) ∧ detNorm F 1 ((k⁻¹ : Γ) * x) < Real.exp 1) ↔
        x ∈ S
      rw [detNorm_rationalSubgroup_mul F 1 (k⁻¹ : Γ).2]
      rfl
    · rw [Set.inter_comm, ← rationalQuotientHaarMeasure_determinantSlab_eq F 1 hD]
      exact h0
  obtain ⟨z, hz⟩ := exists_detNorm_eq F (Real.exp_pos (1 / 2))
  have hU : IsOpen {g : Points F 1 | 1 < detNorm F 1 g ∧ detNorm F 1 g < Real.exp 1} :=
    (isOpen_lt continuous_const (Unfolding.continuous_detNorm F 1)).inter
      (isOpen_lt (Unfolding.continuous_detNorm F 1) continuous_const)
  have hUne : ({g : Points F 1 | 1 < detNorm F 1 g ∧ detNorm F 1 g < Real.exp 1}).Nonempty := by
    refine ⟨z, ?_, ?_⟩
    · rw [hz]
      exact Real.one_lt_exp_iff.mpr (by norm_num)
    · rw [hz]
      exact Real.exp_lt_exp.mpr (by norm_num)
  have hpos := hU.measure_pos (Measure.haar : Measure (Points F 1)) hUne
  have hle : (Measure.haar : Measure (Points F 1))
      {g : Points F 1 | 1 < detNorm F 1 g ∧ detNorm F 1 g < Real.exp 1} ≤
        (Measure.haar : Measure (Points F 1)) S :=
    measure_mono fun g hg => ⟨hg.1.le, hg.2⟩
  rw [hS0] at hle
  exact hpos.ne' (nonpos_iff_eq_zero.mp hle)

end Volume

section FiberMass

/-- Fiber mass one: for every fundamental domain `D` of `F^×` in `𝔸^×` and every `c > 0`,
`d^×a (D ∩ {c ≤ |a| < e c}) = 1`. -/
theorem ideleMeasure_fundamentalDomain_Ico {D : Set (Points F 1)}
    (hD : IsFundamentalDomain (AdelicGroupPoints.rationalSubgroup F (Scheme F 1)) D
      Measure.haar) {c : ℝ} (hc : 0 < c) :
    ideleMeasure F (D ∩ {z : Points F 1 | c ≤ detNorm F 1 z ∧ detNorm F 1 z < Real.exp 1 * c}) =
      1 := by
  rw [ideleMeasure, Measure.smul_apply, smul_eq_mul,
    ← rationalQuotientHaarMeasure_determinantSlab_eq F 1 hD,
    rationalQuotientHaarMeasure_determinantSlab F hc]
  exact ENNReal.inv_mul_cancel (ideleSlabVolume_ne_zero F) (ideleSlabVolume_ne_top F)

/-- Inversion carries a fundamental domain of `F^×` in `𝔸^×` to a fundamental domain. -/
theorem isFundamentalDomain_preimage_inv {D : Set (Points F 1)}
    (hD : IsFundamentalDomain (AdelicGroupPoints.rationalSubgroup F (Scheme F 1)) D
      Measure.haar) :
    IsFundamentalDomain (AdelicGroupPoints.rationalSubgroup F (Scheme F 1)) (Inv.inv ⁻¹' D)
      Measure.haar := by
  refine hD.preimage_of_equiv (Measure.measurePreserving_inv _).quasiMeasurePreserving
    (e := fun k => k⁻¹) inv_involutive.bijective fun k x => ?_
  change ((k⁻¹ : AdelicGroupPoints.rationalSubgroup F (Scheme F 1)) * x : Points F 1)⁻¹ =
    (k : Points F 1) * x⁻¹
  rw [mul_inv_rev, Subgroup.coe_inv, inv_inv, points_one_mul_comm F x⁻¹]

/-- Fiber mass one for the half-open interval of the other orientation:
`d^×a (D ∩ {c < |a| ≤ e c}) = 1`. -/
theorem ideleMeasure_fundamentalDomain_Ioc {D : Set (Points F 1)}
    (hD : IsFundamentalDomain (AdelicGroupPoints.rationalSubgroup F (Scheme F 1)) D
      Measure.haar) {c : ℝ} (hc : 0 < c) :
    ideleMeasure F (D ∩ {z : Points F 1 | c < detNorm F 1 z ∧ detNorm F 1 z ≤ Real.exp 1 * c}) =
      1 := by
  have hec : 0 < Real.exp 1 * c := mul_pos (Real.exp_pos 1) hc
  have h := ideleMeasure_fundamentalDomain_Ico F (isFundamentalDomain_preimage_inv F hD)
    (inv_pos.mpr hec)
  refine Eq.trans ?_ h
  simp only [ideleMeasure, Measure.smul_apply, smul_eq_mul]
  congr 1
  rw [← Measure.measure_preimage_inv (Measure.haar : Measure (Points F 1))
    (D ∩ {z : Points F 1 | c < detNorm F 1 z ∧ detNorm F 1 z ≤ Real.exp 1 * c})]
  congr 1
  have he : Real.exp 1 * (Real.exp 1 * c)⁻¹ = c⁻¹ := by
    rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ (Real.exp_pos 1).ne', one_mul]
  ext z
  have hz := Unfolding.detNorm_pos F 1 z
  simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_ofPred_eq, detNorm_inv, he]
  constructor
  · rintro ⟨hzD, h1, h2⟩
    exact ⟨hzD, (inv_le_comm₀ hec hz).mpr h2, (lt_inv_comm₀ hc hz).mp h1⟩
  · rintro ⟨hzD, h1, h2⟩
    exact ⟨hzD, (lt_inv_comm₀ hc hz).mpr h2, (inv_le_comm₀ hec hz).mp h1⟩

end FiberMass

section Statement

/-- The idele slab facts behind the normalization of the equal-rank integral, for every number
field: `0 < ideleSlabVolume F < ∞`; for every `c > 0` the slab `F^× \ {c ≤ |a| < e c}` has volume
`ideleSlabVolume F`; and for every fundamental domain `D` of `F^×` in `𝔸^×` and every `c > 0`,
`d^×a (D ∩ {c ≤ |a| < e c}) = 1` and `d^×a (D ∩ {c < |a| ≤ e c}) = 1`. -/
def IdeleFiberMassStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K],
    ideleSlabVolume K ≠ 0 ∧ ideleSlabVolume K ≠ ⊤ ∧
      (∀ c : ℝ, 0 < c →
        AdelicGroupPoints.rationalQuotientHaarMeasure K (Scheme K 1)
          (determinantSlab K 1 c (Real.exp 1 * c)) = ideleSlabVolume K) ∧
      ∀ D : Set (Points K 1),
        IsFundamentalDomain (AdelicGroupPoints.rationalSubgroup K (Scheme K 1)) D
          Measure.haar →
        ∀ c : ℝ, 0 < c →
          ideleMeasure K
              (D ∩ {z : Points K 1 | c ≤ detNorm K 1 z ∧ detNorm K 1 z < Real.exp 1 * c}) = 1 ∧
            ideleMeasure K
              (D ∩ {z : Points K 1 | c < detNorm K 1 z ∧ detNorm K 1 z ≤ Real.exp 1 * c}) = 1

/-- Proof of `IdeleFiberMassStatement`. -/
theorem ideleFiberMass : IdeleFiberMassStatement.{u} := fun K _ _ =>
  ⟨ideleSlabVolume_ne_zero K, ideleSlabVolume_ne_top K,
    fun _ hc => rationalQuotientHaarMeasure_determinantSlab K hc,
    fun _ hD _ hc =>
      ⟨ideleMeasure_fundamentalDomain_Ico K hD hc, ideleMeasure_fundamentalDomain_Ioc K hD hc⟩⟩

end Statement

end Langlands.Global.RankinSelbergGlobal
