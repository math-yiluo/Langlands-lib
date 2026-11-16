import Langlands.Global.RankinSelberg.EqualAnalyticIdeleCharacter
import Langlands.Global.RankinSelberg.UnequalAnalyticProjection

/-! # Fibration of `GL_n(F) \ GL_n(𝔸)` over the centre

Let `ζ : 𝔸^× → GL_n(𝔸)` be the scalar embedding `a ↦ a I_n`, `D` the Library fundamental domain
of `GL_n(F)` in `GL_n(𝔸)` and `S = {1 ≤ |det g| < e^n}`.

* The centre of `GL_n(𝔸)` is `ζ(𝔸^×)` (`exists_zeta_eq_of_mem_center`), so a function invariant
  under `GL_n(F)` and under `ζ(𝔸^×)` is invariant under `Z_n(𝔸) GL_n(F)`.
* For every `g`, `{a ∈ D₁ | ζ(a)⁻¹ g ∈ S}` has `d^×a`-measure one, so
  `μ_(GL_n(F)\GL_n(𝔸))` is the image of `μ|_(D ∩ S) ⊗ d^×a|_(D₁)` under `(g, a) ↦ ζ(a) g`
  (`rationalQuotientHaarMeasure_eq_map`).
* Integrals against `centralQuotientMeasure` are integrals over `D ∩ S`
  (`integral_centralQuotientMeasure`, `integrable_centralQuotientMeasure_iff`).
-/

noncomputable section
universe u
open NumberField MeasureTheory Set Langlands Langlands.Global
open scoped CategoryTheory.MonObj ENNReal

namespace Langlands.Global.RankinSelbergGlobal.EqualAnalytic

local instance centralSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance centralSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

variable (F : Type u) [Field F] [NumberField F]

local notation "E" => GeneralLinearGroupPoints.adelicEquiv F
local notation "e" => GeneralLinearGroupPoints.adelicHomeomorph F

/-! ### The scalar embedding -/

/-- The scalar embedding `ζ(a) = a I_n` of `GL_1(𝔸)` in `GL_n(𝔸)`. -/
def zeta (n : ℕ) (a : Points F 1) : Points F n :=
  (e n).symm (AdelicGL.scalar F n (ideleOf F a))

theorem adelicEquiv_zeta (n : ℕ) (a : Points F 1) :
    E n (zeta F n a) = AdelicGL.scalar F n (ideleOf F a) :=
  (e n).apply_symm_apply _

theorem zeta_mul (n : ℕ) (a b : Points F 1) : zeta F n (a * b) = zeta F n a * zeta F n b := by
  simp only [zeta, ideleOf_mul, map_mul]

theorem zeta_one (n : ℕ) : zeta F n 1 = 1 := by
  simp only [zeta, ideleOf_one, map_one]

theorem zeta_inv (n : ℕ) (a : Points F 1) : zeta F n a⁻¹ = (zeta F n a)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← zeta_mul, inv_mul_cancel, zeta_one]

theorem continuous_zeta (n : ℕ) : Continuous (zeta F n) :=
  (e n).symm.continuous.comp ((AdelicGL.scalar F n).continuous.comp (continuous_ideleOf F))

theorem zeta_mul_comm (n : ℕ) (a : Points F 1) (g : Points F n) :
    zeta F n a * g = g * zeta F n a := by
  apply (E n).injective
  rw [map_mul, map_mul, adelicEquiv_zeta]
  exact AdelicGL.scalar_commute F n _ _

theorem detNorm_one_eq (a : Points F 1) :
    detNorm F 1 a = ((IdeleAbsoluteValue.full F (ideleOf F a) : NNReal) : ℝ) := rfl

theorem detNorm_zeta (n : ℕ) (a : Points F 1) : detNorm F n (zeta F n a) = detNorm F 1 a ^ n := by
  rw [UnequalAnalytic.detNorm_eq_absDet, adelicEquiv_zeta, detNorm_one_eq, absDet]
  have h : AdelicGL.determinant F n (AdelicGL.scalar F n (ideleOf F a)) = ideleOf F a ^ n := by
    apply Units.ext
    change Matrix.det (Matrix.scalar (Fin n) ((ideleOf F a : Ideles F) : Adeles F)) = _
    rw [Units.val_pow_eq_pow_val, Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
  rw [h, map_pow, Units.val_pow_eq_pow_val, NNReal.coe_pow]

theorem detNorm_zeta_mul (n : ℕ) (a : Points F 1) (g : Points F n) :
    detNorm F n (zeta F n a * g) = detNorm F 1 a ^ n * detNorm F n g := by
  rw [UnequalAnalytic.detNorm_mul, detNorm_zeta]

theorem log_detNorm_zeta_mul (n : ℕ) (a : Points F 1) (g : Points F n) :
    Real.log (detNorm F n (zeta F n a * g)) = n * logNorm F a + Real.log (detNorm F n g) := by
  rw [detNorm_zeta_mul, Real.log_mul (pow_pos (UnequalAnalytic.detNorm_pos F a) n).ne'
    (UnequalAnalytic.detNorm_pos F g).ne', Real.log_pow, logNorm]

/-! ### The centre -/

/-- Every central element of `GL_n(𝔸)` is a scalar `ζ(a)`. -/
theorem exists_zeta_eq_of_mem_center (n : ℕ) {x : Points F n}
    (hx : x ∈ Subgroup.center (Points F n)) : ∃ a : Points F 1, zeta F n a = x := by
  have hx' : E n x ∈ Subgroup.center (AdelicGL F n) := by
    rw [Subgroup.mem_center_iff]
    intro h
    obtain ⟨y, rfl⟩ := (E n).surjective h
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 hx) y]
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hx'
  obtain ⟨v, hv⟩ := hx'
  refine ⟨(e 1).symm (AdelicGL.scalar F 1 v), ?_⟩
  have hdet : ideleOf F ((e 1).symm (AdelicGL.scalar F 1 v)) = v := by
    apply Units.ext
    change Matrix.det ((E 1) ((e 1).symm (AdelicGL.scalar F 1 v)) : Matrix (Fin 1) (Fin 1)
      (Adeles F)) = _
    rw [show (E 1) ((e 1).symm (AdelicGL.scalar F 1 v)) = AdelicGL.scalar F 1 v from
      (e 1).apply_symm_apply _]
    change Matrix.det (Matrix.scalar (Fin 1) ((v : Ideles F) : Adeles F)) = _
    rw [Matrix.det_fin_one, Matrix.scalar_apply, Matrix.diagonal_apply_eq]
  apply (E n).injective
  rw [adelicEquiv_zeta, hdet]
  exact hv

/-- The subgroup `Z_n(𝔸) GL_n(F)`, as the stabilizer of a function. -/
def invariantSubgroup {n : ℕ} {Z : Type*} (f : Points F n → Z) : Subgroup (Points F n) where
  carrier := {x | ∀ g, f (x * g) = f g}
  mul_mem' {x y} hx hy g := by
    show f (x * y * g) = f g
    rw [mul_assoc, hx, hy]
  one_mem' g := by
    show f (1 * g) = f g
    rw [one_mul]
  inv_mem' {x} hx g := by
    show f (x⁻¹ * g) = f g
    rw [← hx (x⁻¹ * g), mul_inv_cancel_left]

/-- A function invariant under rational points and under scalars is invariant under
`Z_n(𝔸) GL_n(F)`. -/
theorem centralRationalSubgroup_invariant {n : ℕ} {Z : Type*} (f : Points F n → Z)
    (hrat : ∀ (c : RationalGroupPoints F (Scheme F n)) (g : Points F n),
      f (AdelicGroupPoints.rational F (Scheme F n) c * g) = f g)
    (hcent : ∀ (a : Points F 1) (g : Points F n), f (zeta F n a * g) = f g) :
    ∀ (x : centralRationalSubgroup F n) (g : Points F n), f ((x : Points F n) * g) = f g := by
  have hle : centralRationalSubgroup F n ≤ invariantSubgroup F f := by
    refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · obtain ⟨a, rfl⟩ := exists_zeta_eq_of_mem_center F n hx
      exact hcent a
    · obtain ⟨c, rfl⟩ := hx
      exact hrat c
  intro x g
  exact hle x.2 g

/-! ### The fundamental domain and the slab -/

/-- The rational subgroup `GL_n(F)` of `GL_n(𝔸)`. -/
abbrev glRational (n : ℕ) : Subgroup (Points F n) :=
  AdelicGroupPoints.rationalSubgroup F (Scheme F n)

theorem isDiscrete_glRational (n : ℕ) : IsDiscrete (glRational F n : Set (Points F n)) :=
  AdelicGroupPoints.isDiscrete_rationalSubgroup F (Scheme F n)

instance countable_glRational (n : ℕ) : Countable (glRational F n) :=
  LeftCosetSpace.countable_of_isDiscrete _ (isDiscrete_glRational F n)

/-- The Library fundamental domain `D` of `GL_n(F)` in `GL_n(𝔸)`. -/
def glDomain (n : ℕ) : Set (Points F n) :=
  LeftCosetSpace.fundamentalDomain (glRational F n) (isDiscrete_glRational F n)

theorem measurableSet_glDomain (n : ℕ) : MeasurableSet (glDomain F n) :=
  LeftCosetSpace.measurableSet_fundamentalDomain _ _

theorem isFundamentalDomain_glDomain (n : ℕ) (ν : Measure (Points F n)) :
    IsFundamentalDomain (glRational F n) (glDomain F n) ν :=
  LeftCosetSpace.isFundamentalDomain _ _ ν

theorem rationalQuotientHaarMeasure_eq_quotientMeasure (n : ℕ) :
    AdelicGroupPoints.rationalQuotientHaarMeasure F (Scheme F n) =
      LeftCosetSpace.quotientMeasure (glRational F n) Measure.haar (glDomain F n) :=
  AdelicGroupPoints.rationalQuotientHaarMeasure_eq F (Scheme F n)
    (isFundamentalDomain_glDomain F n Measure.haar)

theorem detNorm_glRational_mul {n : ℕ} (c : glRational F n) (g : Points F n) :
    detNorm F n ((c : Points F n) * g) = detNorm F n g := by
  obtain ⟨_, c', rfl⟩ := c
  exact UnequalAnalytic.detNorm_rational_mul F c' g

/-- The slab `S = {1 ≤ |det g| < e^n}`. -/
def glSlab (n : ℕ) : Set (Points F n) :=
  (fun g => detNorm F n g) ⁻¹' Ico 1 (Real.exp n)

theorem measurableSet_glSlab (n : ℕ) : MeasurableSet (glSlab F n) :=
  measurableSet_Ico.preimage (UnequalAnalytic.continuous_detNorm F n).measurable

theorem glSlab_invariant (n : ℕ) (c : glRational F n) (g : Points F n) :
    (c : Points F n) * g ∈ glSlab F n ↔ g ∈ glSlab F n := by
  simp only [glSlab, mem_preimage, detNorm_glRational_mul]

theorem determinantSlab_eq (n : ℕ) :
    determinantSlab F n 1 (Real.exp n) = LeftCosetSpace.mk (glRational F n) '' glSlab F n := rfl

theorem mem_Ico_one_exp_iff {t r : ℝ} (ht : 0 < t) :
    t ∈ Ico 1 (Real.exp r) ↔ Real.log t ∈ Ico 0 r := by
  simp only [mem_Ico, Real.log_nonneg_iff ht, Real.log_lt_iff_lt_exp ht]

/-- **The fibers have measure one.** -/
theorem ideleMeasure_fiber (n : ℕ) (hn : 0 < n) (g : Points F n) :
    ideleMeasure F (ideleDomain F ∩ {a | (zeta F n a)⁻¹ * g ∈ glSlab F n}) = 1 := by
  set L := Real.log (detNorm F n g)
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hset : {a | (zeta F n a)⁻¹ * g ∈ glSlab F n} =
      logNorm F ⁻¹' Ioc (L / n - 1) (L / n) := by
    ext a
    have hlog : logNorm F a⁻¹ = -logNorm F a := by
      have h1 := detNorm_one_mul F a a⁻¹
      rw [mul_inv_cancel] at h1
      have h2 : detNorm F 1 (1 : Points F 1) = 1 := by
        have h3 := detNorm_one_mul F 1 1
        rw [one_mul] at h3
        have hp := UnequalAnalytic.detNorm_pos F (1 : Points F 1)
        field_simp at h3
        linarith [h3]
      rw [h2] at h1
      have hpa := UnequalAnalytic.detNorm_pos F a
      have hpa' := UnequalAnalytic.detNorm_pos F a⁻¹
      rw [logNorm, logNorm, show detNorm F 1 a⁻¹ = (detNorm F 1 a)⁻¹ from
        eq_inv_of_mul_eq_one_right h1.symm, Real.log_inv]
    simp only [mem_ofPred_eq, glSlab, mem_preimage, ← zeta_inv]
    rw [mem_Ico_one_exp_iff (UnequalAnalytic.detNorm_pos F _), log_detNorm_zeta_mul, hlog]
    simp only [mem_Ico, mem_Ioc]
    constructor
    · rintro ⟨h1, h2⟩
      constructor
      · rw [sub_lt_iff_lt_add, div_lt_iff₀ hn']; nlinarith
      · rw [le_div_iff₀ hn']; nlinarith
    · rintro ⟨h1, h2⟩
      rw [sub_lt_iff_lt_add, div_lt_iff₀ hn'] at h1
      rw [le_div_iff₀ hn'] at h2
      constructor <;> nlinarith
  rw [hset, ideleMeasure_logNorm_preimage F measurableSet_Ioc, Real.volume_Ioc]
  simp

/-! ### The quotient measure as an image -/

/-- The map `(g, a) ↦ GL_n(F) ζ(a) g`. -/
def fibrationMap (n : ℕ) (p : Points F n × Points F 1) :
    AdelicGroupPoints.RationalQuotient F (Scheme F n) :=
  LeftCosetSpace.mk (glRational F n) (zeta F n p.2 * p.1)

theorem measurable_fibrationMap (n : ℕ) : Measurable (fibrationMap F n) :=
  (LeftCosetSpace.measurable_mk _).comp
    (((continuous_zeta F n).measurable.comp measurable_snd).mul measurable_fst)

/-- The product measure `μ|_(D ∩ S) ⊗ d^×a|_(D₁)`. -/
def fibrationMeasure (n : ℕ) : Measure (Points F n × Points F 1) :=
  ((Measure.haar : Measure (Points F n)).restrict (glDomain F n ∩ glSlab F n)).prod
    ((ideleMeasure F).restrict (ideleDomain F))

instance fibrationMeasure_sFinite (n : ℕ) : SFinite (fibrationMeasure F n) := by
  unfold fibrationMeasure; infer_instance

/-- **The quotient measure is the image of the product measure.** -/
theorem rationalQuotientHaarMeasure_eq_map (n : ℕ) (hn : 0 < n) :
    AdelicGroupPoints.rationalQuotientHaarMeasure F (Scheme F n) =
      Measure.map (fibrationMap F n) (fibrationMeasure F n) := by
  rw [rationalQuotientHaarMeasure_eq_quotientMeasure]
  exact quotientMeasure_eq_map_fibration (glRational F n) Measure.haar (ideleMeasure F)
    (zeta F n) (isFundamentalDomain_glDomain F n _) (measurableSet_glDomain F n)
    (continuous_zeta F n).measurable (zeta_mul_comm F n) (ideleDomain F)
    (measurableSet_glSlab F n) (glSlab_invariant F n) (ideleMeasure_fiber F n hn)

theorem lintegral_rationalQuotient_eq (n : ℕ) (hn : 0 < n)
    (f : AdelicGroupPoints.RationalQuotient F (Scheme F n) → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ x, f x ∂AdelicGroupPoints.rationalQuotientHaarMeasure F (Scheme F n) =
      ∫⁻ g in glDomain F n ∩ glSlab F n, ∫⁻ a in ideleDomain F,
        f (LeftCosetSpace.mk (glRational F n) (zeta F n a * g)) ∂ideleMeasure F ∂Measure.haar := by
  rw [rationalQuotientHaarMeasure_eq_map F n hn, lintegral_map hf (measurable_fibrationMap F n),
    fibrationMeasure]
  exact lintegral_prod (fun p => f (fibrationMap F n p))
    (hf.comp (measurable_fibrationMap F n)).aemeasurable

theorem integrable_rationalQuotient_iff (n : ℕ) (hn : 0 < n)
    {f : AdelicGroupPoints.RationalQuotient F (Scheme F n) → ℂ}
    (hf : AEStronglyMeasurable f (AdelicGroupPoints.rationalQuotientHaarMeasure F (Scheme F n))) :
    Integrable f (AdelicGroupPoints.rationalQuotientHaarMeasure F (Scheme F n)) ↔
      Integrable (fun p => f (fibrationMap F n p)) (fibrationMeasure F n) := by
  rw [rationalQuotientHaarMeasure_eq_map F n hn] at hf ⊢
  exact integrable_map_measure hf (measurable_fibrationMap F n).aemeasurable

theorem integral_rationalQuotient_eq (n : ℕ) (hn : 0 < n)
    {f : AdelicGroupPoints.RationalQuotient F (Scheme F n) → ℂ}
    (hf : AEStronglyMeasurable f (AdelicGroupPoints.rationalQuotientHaarMeasure F (Scheme F n)))
    (hi : Integrable f (AdelicGroupPoints.rationalQuotientHaarMeasure F (Scheme F n))) :
    ∫ x, f x ∂AdelicGroupPoints.rationalQuotientHaarMeasure F (Scheme F n) =
      ∫ g in glDomain F n ∩ glSlab F n, ∫ a in ideleDomain F,
        f (LeftCosetSpace.mk (glRational F n) (zeta F n a * g)) ∂ideleMeasure F ∂Measure.haar := by
  have hi' := (integrable_rationalQuotient_iff F n hn hf).1 hi
  rw [rationalQuotientHaarMeasure_eq_map F n hn] at hf ⊢
  rw [integral_map (measurable_fibrationMap F n).aemeasurable hf, fibrationMeasure,
    integral_prod _ hi']
  rfl

/-! ### The central quotient -/

theorem toCentralQuotient_mk (n : ℕ) (g : Points F n) :
    toCentralQuotient F n (LeftCosetSpace.mk (glRational F n) g) =
      LeftCosetSpace.mk (centralRationalSubgroup F n) g := rfl

theorem preimage_determinantSlab (n : ℕ) :
    LeftCosetSpace.mk (glRational F n) ⁻¹' determinantSlab F n 1 (Real.exp n) = glSlab F n :=
  preimage_image_mk_of_invariant _ (glSlab_invariant F n)

theorem measurableSet_determinantSlab (n : ℕ) :
    MeasurableSet (determinantSlab F n 1 (Real.exp n)) := by
  rw [determinantSlab_eq]
  exact LeftCosetSpace.measurableSet_image_mk _ (measurableSet_glSlab F n)

/-- The restriction of the quotient measure to the slab is the image of `μ|_(D ∩ S)`. -/
theorem restrict_determinantSlab (n : ℕ) :
    (AdelicGroupPoints.rationalQuotientHaarMeasure F (Scheme F n)).restrict
        (determinantSlab F n 1 (Real.exp n)) =
      Measure.map (LeftCosetSpace.mk (glRational F n))
        ((Measure.haar : Measure (Points F n)).restrict (glDomain F n ∩ glSlab F n)) := by
  rw [rationalQuotientHaarMeasure_eq_quotientMeasure, LeftCosetSpace.quotientMeasure,
    Measure.restrict_map (LeftCosetSpace.measurable_mk _) (measurableSet_determinantSlab F n),
    preimage_determinantSlab, Measure.restrict_restrict (measurableSet_glSlab F n), inter_comm]

theorem centralQuotientMeasure_eq_map (n : ℕ) :
    centralQuotientMeasure F n =
      Measure.map (LeftCosetSpace.mk (centralRationalSubgroup F n))
        ((Measure.haar : Measure (Points F n)).restrict (glDomain F n ∩ glSlab F n)) := by
  rw [centralQuotientMeasure, restrict_determinantSlab,
    Measure.map_map (measurable_toCentralQuotient F n) (LeftCosetSpace.measurable_mk _)]
  rfl

theorem measurable_mk_central (n : ℕ) :
    Measurable (LeftCosetSpace.mk (centralRationalSubgroup F n)) :=
  LeftCosetSpace.measurable_mk _

/-- **Integrals over the central quotient are integrals over `D ∩ S`.** For `f` invariant under
`Z_n(𝔸) GL_n(F)` and strongly measurable, the function `q ↦ f q.out` is integrable for
`centralQuotientMeasure` iff `f` is integrable on `D ∩ S`, with the same integral. -/
theorem integrable_centralQuotientMeasure_iff (n : ℕ) {f : Points F n → ℂ}
    (hfm : StronglyMeasurable f)
    (hf : ∀ (x : centralRationalSubgroup F n) (g : Points F n), f ((x : Points F n) * g) = f g) :
    Integrable (fun q : CentralQuotient F n => f (Quotient.out q)) (centralQuotientMeasure F n) ↔
      IntegrableOn f (glDomain F n ∩ glSlab F n) Measure.haar := by
  have hfun : (fun q : CentralQuotient F n => f (Quotient.out q)) =
      LeftCosetSpace.lift (centralRationalSubgroup F n) f hf :=
    funext fun q => (UnequalAnalytic.lift_eq_out _ f hf q).symm
  have hm : StronglyMeasurable (LeftCosetSpace.lift (centralRationalSubgroup F n) f hf) := by
    refine (measurable_from_quotient.2 ?_).stronglyMeasurable
    exact hfm.measurable
  rw [hfun, centralQuotientMeasure_eq_map, integrable_map_measure
    (hm.aestronglyMeasurable) (measurable_mk_central F n).aemeasurable]
  rfl

theorem integral_centralQuotientMeasure (n : ℕ) {f : Points F n → ℂ}
    (hfm : StronglyMeasurable f)
    (hf : ∀ (x : centralRationalSubgroup F n) (g : Points F n), f ((x : Points F n) * g) = f g) :
    ∫ q : CentralQuotient F n, f (Quotient.out q) ∂centralQuotientMeasure F n =
      ∫ g in glDomain F n ∩ glSlab F n, f g ∂Measure.haar := by
  have hfun : (fun q : CentralQuotient F n => f (Quotient.out q)) =
      LeftCosetSpace.lift (centralRationalSubgroup F n) f hf :=
    funext fun q => (UnequalAnalytic.lift_eq_out _ f hf q).symm
  have hm : StronglyMeasurable (LeftCosetSpace.lift (centralRationalSubgroup F n) f hf) := by
    refine (measurable_from_quotient.2 ?_).stronglyMeasurable
    exact hfm.measurable
  rw [hfun, centralQuotientMeasure_eq_map, integral_map (measurable_mk_central F n).aemeasurable
    hm.aestronglyMeasurable]
  rfl

end Langlands.Global.RankinSelbergGlobal.EqualAnalytic
