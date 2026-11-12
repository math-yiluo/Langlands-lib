import Langlands.Automorphic.CuspidalUnitaryCompactForm
import Langlands.Automorphic.CuspidalL2.SiegelCover
import Langlands.Automorphic.AssociatedFactorStatement
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Deriv.Star

/-! # The determinant-band form of a cuspidal realization is a unitary form

For an actual cuspidal operator realization with unitary central character, the
determinant-band `L²` form is invariant under every adelic right translation, hence
under the compact action, and every real Lie direction acts skew-adjointly. -/

noncomputable section
universe uF u
set_option autoImplicit false

open CategoryTheory _root_.AlgebraicGeometry MeasureTheory Filter Topology
open scoped NNReal ENNReal

/-! ### One-parameter subgroups of the archimedean group -/

namespace Langlands.Global.ArchimedeanGL

open scoped Classical Matrix.Norms.Operator

set_option backward.isDefEq.respectTransparency false

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

/-- The one-parameter subgroup `t ↦ exp (t X)` of the archimedean matrix group. -/
def oneParameter (X : RealLieAlgebra K n) (t : ℝ) : ArchimedeanGL K n where
  val := NormedSpace.exp (t • realLieAlgebraToMatrix K n X)
  inv := NormedSpace.exp (-(t • realLieAlgebraToMatrix K n X))
  val_inv := by
    rw [← NormedSpace.exp_add_of_commute (Commute.refl _).neg_right, add_neg_cancel,
      NormedSpace.exp_zero]
  inv_val := by
    rw [← NormedSpace.exp_add_of_commute (Commute.refl _).neg_left, neg_add_cancel,
      NormedSpace.exp_zero]

@[simp]
theorem oneParameter_val (X : RealLieAlgebra K n) (t : ℝ) :
    (oneParameter K n X t : ArchimedeanMatrix K n) =
      NormedSpace.exp (t • realLieAlgebraToMatrix K n X) := rfl

theorem oneParameter_zero (X : RealLieAlgebra K n) : oneParameter K n X 0 = 1 := by
  apply Units.ext
  rw [oneParameter_val, zero_smul, NormedSpace.exp_zero, Units.val_one]

theorem hasDerivAt_oneParameter_val (X : RealLieAlgebra K n) (t : ℝ) :
    HasDerivAt (fun s => (oneParameter K n X s : ArchimedeanMatrix K n))
      ((oneParameter K n X t : ArchimedeanMatrix K n) * realLieAlgebraToMatrix K n X) t :=
  hasDerivAt_exp_smul_const (realLieAlgebraToMatrix K n X) t

theorem continuous_oneParameter (X : RealLieAlgebra K n) : Continuous (oneParameter K n X) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · exact continuous_iff_continuousAt.mpr fun t =>
      (hasDerivAt_oneParameter_val K n X t).continuousAt
  · exact NormedSpace.exp_continuous.comp ((continuous_id.smul continuous_const).neg)

/-- The same one-parameter subgroup in completion coordinates. -/
def infiniteOneParameter (X : RealLieAlgebra K n) (t : ℝ) :
    Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing K) :=
  (archimedeanGLCoordinates K n).symm (oneParameter K n X t)

theorem infiniteOneParameter_zero (X : RealLieAlgebra K n) :
    infiniteOneParameter K n X 0 = 1 := by
  rw [infiniteOneParameter, oneParameter_zero, map_one]

theorem continuous_infiniteOneParameter (X : RealLieAlgebra K n) :
    Continuous (infiniteOneParameter K n X) :=
  (archimedeanGLCoordinates K n).symm.continuous.comp (continuous_oneParameter K n X)

/-- A smooth function differentiates along the one-parameter subgroup by the actual
real Lie derivative. -/
theorem hasDerivAt_smooth_oneParameter (s : SmoothFunctions K n) (X : RealLieAlgebra K n)
    (a : Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing K)) (t : ℝ) :
    HasDerivAt (fun u => s.val (a * infiniteOneParameter K n X u))
      ((smoothDifferential K n X s).val (a * infiniteOneParameter K n X t)) t := by
  set A : ArchimedeanMatrix K n := (archimedeanGLCoordinates K n a : ArchimedeanMatrix K n)
  have key : ∀ u, s.val (a * infiniteOneParameter K n X u) =
      coordinateExtension K n s (A * (oneParameter K n X u : ArchimedeanMatrix K n)) := by
    intro u
    have h := coordinateExtension_apply K n s
      (archimedeanGLCoordinates K n a * oneParameter K n X u)
    rw [Units.val_mul] at h
    rw [h, map_mul, ContinuousMulEquiv.symm_apply_apply]
    rfl
  have hcoord : (archimedeanGLCoordinates K n (a * infiniteOneParameter K n X t) :
      ArchimedeanMatrix K n) = A * (oneParameter K n X t : ArchimedeanMatrix K n) := by
    rw [infiniteOneParameter, map_mul, ContinuousMulEquiv.apply_symm_apply, Units.val_mul]
  have hd : HasFDerivAt (coordinateExtension K n s)
      (fderiv ℝ (coordinateExtension K n s)
        (A * (oneParameter K n X t : ArchimedeanMatrix K n)))
      (A * (oneParameter K n X t : ArchimedeanMatrix K n)) := by
    have h := (coordinateExtension_contDiffAt K n s
      (archimedeanGLCoordinates K n a * oneParameter K n X t)).differentiableAt (by simp)
    rw [Units.val_mul] at h
    exact h.hasFDerivAt
  have hc := hd.comp_hasDerivAt t ((hasDerivAt_oneParameter_val K n X t).const_mul A)
  have hfun : (fun u => s.val (a * infiniteOneParameter K n X u)) =
      coordinateExtension K n s ∘ fun y => A * (oneParameter K n X y : ArchimedeanMatrix K n) :=
    funext key
  rw [smoothDifferential_apply, hcoord, mul_assoc, hfun]
  exact hc

end Langlands.Global.ArchimedeanGL

/-! ### Differentiation of realized vectors along a one-parameter subgroup -/

namespace Langlands.Automorphic.OperatorRealization

open Langlands.Global ContinuousRationalFunctions

variable {F : Type uF} [Field F] [NumberField F] {n : ℕ} (S : OperatorRealization F n)

local instance : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance : AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance instAddCommGroupSpace_cuspidalUnitaryForm :
    AddCommGroup S.Space := Submodule.addCommGroup _

/-- The differential operator of a real Lie direction. -/
abbrev lieOperator (X : ArchimedeanGL.RealLieAlgebra F n) : Module.End ℂ S.Space :=
  S.envelopingAction (ArchimedeanGL.envelopingGenerator F n (ArchimedeanGL.complexify F n X))

theorem mul_ofInfinite_eq_pair (x : AdelicGL F n) (c : InfiniteAdelicGL F n) :
    x * AdelicGL.ofInfinite F n c =
      AdelicGL.pair F n (AdelicGL.infinite F n x * c) (AdelicGL.finite F n x) :=
  AdelicGL.ext_infinite_finite F n
    (by rw [AdelicGL.infinite_pair, map_mul, AdelicGL.infinite_ofInfinite])
    (by rw [AdelicGL.finite_pair, map_mul, AdelicGL.finite_ofInfinite, mul_one])

/-- The value of a real Lie derivative is the smooth derivative of the archimedean slice. -/
theorem evaluate_lieOperator_pair (X : ArchimedeanGL.RealLieAlgebra F n) (f : S.Space)
    (a : InfiniteAdelicGL F n) (b : FiniteAdelicGL F n) :
    evaluate F n (S.toContinuous (S.lieOperator X f)) (AdelicGL.pair F n a b) =
      (ArchimedeanGL.smoothDifferential F n X
        (finiteSmoothSlice F n b (S.ambient f))).val a := by
  rw [S.evaluate_toContinuous, S.ambient_envelopingAction,
    evaluate_finiteSmoothEnvelopingAction, ArchimedeanGL.envelopingAction_real_generator]

/-- Realized vectors differentiate along `x · exp (t X)` by the real Lie action. -/
theorem hasDerivAt_evaluate_oneParameter (X : ArchimedeanGL.RealLieAlgebra F n) (f : S.Space)
    (x : AdelicGL F n) (t : ℝ) :
    HasDerivAt (fun u => evaluate F n (S.toContinuous f)
        (x * AdelicGL.ofInfinite F n (ArchimedeanGL.infiniteOneParameter F n X u)))
      (evaluate F n (S.toContinuous (S.lieOperator X f))
        (x * AdelicGL.ofInfinite F n (ArchimedeanGL.infiniteOneParameter F n X t))) t := by
  have h := ArchimedeanGL.hasDerivAt_smooth_oneParameter F n
    (finiteSmoothSlice F n (AdelicGL.finite F n x) (S.ambient f)) X (AdelicGL.infinite F n x) t
  simp only [finiteSmoothSlice_apply] at h
  rw [mul_ofInfinite_eq_pair, S.evaluate_lieOperator_pair]
  simp only [mul_ofInfinite_eq_pair, S.evaluate_toContinuous]
  exact h

end Langlands.Automorphic.OperatorRealization

/-! ### Translation invariance of the band form -/

namespace Langlands.Automorphic.OperatorDeterminantSlice

open Langlands.Global ContinuousRationalFunctions NumberField
open scoped CategoryTheory.MonObj

variable (F : Type uF) [Field F] [NumberField F] (n : ℕ)

local instance unitaryFormIsAffine : IsAffine (matrixGroupScheme F n).X.left :=
  Langlands.GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)
local instance unitaryFormSmooth : Smooth (matrixGroupScheme F n).X.hom :=
  Langlands.GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of F)
local instance : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance : AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _

theorem translate_one (q : Quotient F n) : translate F n 1 q = q := by
  obtain ⟨x, rfl⟩ := point_surjective F n q
  rw [translate_point, mul_one]

variable (S : OperatorRealization F n)
local instance : AddCommGroup S.Space := Submodule.addCommGroup _

set_option maxHeartbeats 1500000 in
/-- The band integral of the pointwise Hermitian product is invariant under every adelic
right translation, after normalizing the determinant by a central scalar. -/
theorem integral_inner_translate (hn : n ≠ 0) (measure : Measure (Quotient F n))
    (χ : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ)
    (hχ : ∀ x, ‖(χ x : ℂ)‖ = 1) (hS : S.HasCentralCharacter χ)
    (hmeasure : ∀ g : AdelicGL F n,
      AdelicBlockDeterminantCharacter.determinantNorm F n g = 1 →
        MeasurePreserving (translate F n g) measure measure)
    (a : AdelicGL F n) (f g : S.Space) :
    ∫ q, inner ℂ (toQuotient F n S f (translate F n a q))
        (toQuotient F n S g (translate F n a q)) ∂measure.restrict (band F n) =
      ∫ q, inner ℂ (toQuotient F n S f q) (toQuotient F n S g q)
        ∂measure.restrict (band F n) := by
  obtain ⟨z, hz⟩ := exists_normalized_rightTranslate F n hn a
  let b := AdelicGL.scalar F n z * a
  have hb := measurePreserving_translate_band F n measure b hz (hmeasure b hz)
  calc
    _ = ∫ q, inner ℂ (toQuotient F n S f (translate F n b q))
        (toQuotient F n S g (translate F n b q)) ∂measure.restrict (band F n) := by
      apply integral_congr_ae
      filter_upwards [] with q
      dsimp only [b]
      rw [toQuotient_central F n S χ hS, toQuotient_central F n S χ hS]
      exact (inner_phase _ _ _ (hχ _)).symm
    _ = _ := hb.integral_comp
      (translate F n b).toMeasurableEquiv.measurableEmbedding
      (fun q => inner ℂ (toQuotient F n S f q) (toQuotient F n S g q))

end Langlands.Automorphic.OperatorDeterminantSlice

/-! ### Uniform square integrability over compact right translates -/

namespace Langlands.Automorphic.OperatorRealization

open scoped Classical Pointwise
open Langlands.Global Langlands.Automorphic.CuspidalL2 ContinuousRationalFunctions

variable {F : Type uF} [Field F] [NumberField F] {n : ℕ} (S : OperatorRealization F n)
variable [MeasurableSpace (AdelicGL F n)] [BorelSpace (AdelicGL F n)]

/-- **Uniform square integrability on a determinant band.** The covering set of
`exists_band_cover` also bounds, uniformly over right translations by a fixed compact set
`Γ`, every function dominated pointwise by such a translate of a realized vector. -/
theorem exists_band_cover_uniform [CompactSpace (AdeleQuotient F)] (hS : S.IsCuspidal)
    {lo hi : ℝ} (hlo : 0 < lo) (Γ : Set (AdelicGL F n)) (hΓ : IsCompact Γ) :
    ∃ t : Set (AdelicGL F n), MeasurableSet t ∧
      (∀ g : AdelicGL F n, lo ≤ absDet F n g → absDet F n g ≤ hi →
        ∃ γr : RationalGL F n, AdelicGL.rational F n γr * g ∈ t) ∧
      ∀ (ν : Measure (AdelicGL F n)) [ν.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts ν]
        (f : S.Space) (Φ : AdelicGL F n → ℝ≥0∞),
        (∀ x, ∃ c ∈ Γ, Φ x ≤ ‖evaluate F n (S.toContinuous f) (x * c)‖ₑ) →
        (∫⁻ x in t, Φ x ^ 2 ∂ν) < ⊤ := by
  have := adelicGL_t2Space F n
  obtain ⟨Q₁, K, hQ₁, hK, hdec⟩ := exists_siegelDecomposition F n
  obtain ⟨L, hL⟩ : ∃ L : ℝ, ∀ q ∈ Q₁, |Real.log (absDet F n q)| ≤ L :=
    (hQ₁.image (continuous_abs.comp ((continuous_absDet F n).log
      fun g => (absDet_pos F n g).ne'))).bddAbove.elim
      fun L hL => ⟨L, fun q hq => hL ⟨q, hq, rfl⟩⟩
  set R₀ : ℝ := max |Real.log lo| |Real.log hi| + L with hR₀
  set Q₂ : Set (AdelicGL F n) := (fun p : (Fin n → ℝ) × AdelicGL F n =>
    AdelicGL.ofInfinite F n (torInf F n p.1) * p.2) ''
      ((Set.univ.pi fun _ => Set.Icc (0 : ℝ) 1) ×ˢ Q₁) with hQ₂def
  have hQ₂ : IsCompact Q₂ := ((isCompact_univ_pi fun _ => isCompact_Icc).prod hQ₁).image
    (((map_continuous (AdelicGL.ofInfinite F n)).comp
      ((continuous_torInf F n).comp continuous_fst)).mul continuous_snd)
  let ι := {m : Fin n → ℤ // Chamber (K + 1) (fun i => (m i : ℝ)) ∧ |∑ i, (m i : ℝ)| ≤ R₀ + n}
  let a : ι → AdelicGL F n := fun m => AdelicGL.ofInfinite F n (torInf F n fun i => (m.1 i : ℝ))
  refine ⟨leftTranslateCover a Q₂, measurableSet_leftTranslateCover a hQ₂, ?_, ?_⟩
  · intro g hlog hhig
    obtain ⟨γr, x, q, hq, hγ, hx⟩ := hdec g
    have hRx : |∑ i, x i| ≤ R₀ := by
      have h1 := abs_sum_le_of_absDet F n x q
      rw [← hγ, absDet_rational_mul] at h1
      have hl := Real.log_le_log hlo hlog
      have hh := Real.log_le_log (absDet_pos F n g) hhig
      have h2 : |Real.log (absDet F n g)| ≤ max |Real.log lo| |Real.log hi| :=
        abs_le.mpr ⟨by linarith [neg_abs_le (Real.log lo), le_max_left |Real.log lo| |Real.log hi|],
          by linarith [le_abs_self (Real.log hi), le_max_right |Real.log lo| |Real.log hi|]⟩
      linarith [hL q hq]
    obtain ⟨hc, hs⟩ := floor_chamber x hx hRx
    have hxy : (fun i => ((⌊x i⌋ : ℤ) : ℝ)) + (fun i => Int.fract (x i)) = x :=
      funext fun i => Int.floor_add_fract (x i)
    refine ⟨γr, Set.mem_iUnion.mpr ⟨⟨fun i => ⌊x i⌋, hc, hs⟩,
      AdelicGL.ofInfinite F n (torInf F n fun i => Int.fract (x i)) * q,
      ⟨(fun i => Int.fract (x i), q),
        ⟨fun i _ => ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩, hq⟩, rfl⟩, ?_⟩⟩
    show AdelicGL.ofInfinite F n (torInf F n fun i => ((⌊x i⌋ : ℤ) : ℝ)) *
      (AdelicGL.ofInfinite F n (torInf F n fun i => Int.fract (x i)) * q) =
        AdelicGL.rational F n γr * g
    rw [hγ, ← mul_assoc, ← map_mul, ← torInf_add, hxy]
  · intro ν _ _ f Φ hΦ
    refine (S.exists_chamber_decay hS f (Q₁ * Γ) (hQ₁.mul hΓ) (K := K + 2)
      (R := R₀ + 2 * n) (by linarith) zero_le_one).elim fun C hC => ?_
    let b : ι → ℝ≥0 := fun m =>
      ⟨|C| * Real.exp n * Real.exp (-(∑ i, |(m.1 i : ℝ)|)), by positivity⟩
    have hsum : Summable fun m => b m ^ 2 :=
      NNReal.summable_coe.mp
        ((summable_sq_lattice_bound _ (|C| * Real.exp n)).congr fun m => by
          rw [NNReal.coe_pow]
          rfl)
    refine lintegral_leftTranslateCover_lt_top ν a Q₂ hQ₂.measure_lt_top
      (fun x => Φ x ^ 2) (fun m => ((b m ^ 2 : ℝ≥0) : ℝ≥0∞)) ?_
      (ENNReal.tsum_coe_ne_top_iff_summable.mpr hsum).lt_top
    intro m x hx
    obtain ⟨c, hcΓ, hΦx⟩ := hΦ (a m * x)
    refine hx.elim fun p hp => ?_
    have key := S.norm_le_on_lattice_translate f hC (fun i => (m.1 i : ℝ)) p.1
      (fun i => hp.1.1 i (Set.mem_univ i)) m.2.1 m.2.2 (p.2 * c)
      (Set.mul_mem_mul hp.1.2 hcΓ)
    have hx' : a m * x * c = AdelicGL.ofInfinite F n (torInf F n fun i => (m.1 i : ℝ)) *
        (AdelicGL.ofInfinite F n (torInf F n p.1) * (p.2 * c)) := by
      rw [← hp.2]
      simp only [a, mul_assoc]
    rw [ENNReal.coe_pow]
    refine pow_le_pow_left₀ bot_le (hΦx.trans ?_) 2
    rw [hx']
    refine enorm_le_coe.mpr ?_
    rw [← NNReal.coe_le_coe, coe_nnnorm]
    exact key

end Langlands.Automorphic.OperatorRealization

/-! ### Supremum functions along a one-parameter subgroup -/

namespace Langlands.Automorphic.OperatorDeterminantSlice

open Langlands.Global ContinuousRationalFunctions NumberField
open scoped CategoryTheory.MonObj

variable (F : Type uF) [Field F] [NumberField F] (n : ℕ)

local instance : IsAffine (matrixGroupScheme F n).X.left :=
  Langlands.GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)
local instance : Smooth (matrixGroupScheme F n).X.hom :=
  Langlands.GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of F)
local instance : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance : AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _

theorem continuous_point : Continuous (point F n) :=
  (LeftCosetSpace.continuous_mk _).comp
    (GeneralLinearGroupPoints.adelicHomeomorph F n).symm.continuous

theorem point_adelicHomeomorph (x : AdelicGroupPoints F (matrixGroupScheme F n)) :
    point F n (GeneralLinearGroupPoints.adelicHomeomorph F n x) =
      LeftCosetSpace.mk (AdelicGroupPoints.rationalSubgroup F (matrixGroupScheme F n)) x := by
  rw [point, ContinuousMulEquiv.symm_apply_apply]

section Cover

variable [MeasurableSpace (AdelicGL F n)] [BorelSpace (AdelicGL F n)]

/-- A matrix covering set controls the band integral of any continuous quotient function. -/
theorem lintegral_band_le_cover_of_continuous (φ : Quotient F n → ℝ) (hφ : Continuous φ)
    (t : Set (AdelicGL F n)) (ht : MeasurableSet t)
    (hcover : ∀ x : AdelicGL F n,
      1 ≤ ((AdelicBlockDeterminantCharacter.determinantNorm F n x : ℝ≥0) : ℝ) ∧
        ((AdelicBlockDeterminantCharacter.determinantNorm F n x : ℝ≥0) : ℝ) ≤ 2 →
      ∃ γr : RationalGL F n, AdelicGL.rational F n γr * x ∈ t) :
    ∫⁻ q in band F n, ‖φ q‖ₑ ^ 2 ∂quotientHaarMeasure F n ≤
      ∫⁻ x in t, ‖φ (point F n x)‖ₑ ^ 2 ∂matrixHaarMeasure F n := by
  let e := GeneralLinearGroupPoints.adelicHomeomorph F n
  let Γ := AdelicGroupPoints.rationalSubgroup F (matrixGroupScheme F n)
  have hcov : ∀ x : AdelicGroupPoints F (matrixGroupScheme F n),
      LeftCosetSpace.mk Γ x ∈ band F n → ∃ γr : Γ, (γr : _) * x ∈ e ⁻¹' t := by
    intro x hx
    change 1 < (groupDeterminantNorm F n x : ℝ≥0) ∧
      (groupDeterminantNorm F n x : ℝ≥0) < 2 at hx
    obtain ⟨γr, hγ⟩ := hcover (e x) ⟨by exact_mod_cast hx.1.le, by exact_mod_cast hx.2.le⟩
    let r := (GeneralLinearGroupPoints.rationalEquiv F n).symm γr
    refine ⟨⟨AdelicGroupPoints.rational F (matrixGroupScheme F n) r, ⟨r, rfl⟩⟩, ?_⟩
    change e (AdelicGroupPoints.rational F (matrixGroupScheme F n) r * x) ∈ t
    simpa only [e, r, map_mul, GeneralLinearGroupPoints.adelicHomeomorph_rational,
      MulEquiv.apply_symm_apply] using hγ
  have hle := LeftCosetSpace.lintegral_restrict_discreteQuotientMeasure_le Γ
    (AdelicGroupPoints.isDiscrete_rationalSubgroup F (matrixGroupScheme F n))
    Measure.haar (band F n) (measurableSet_band F n) (e ⁻¹' t)
    (ht.preimage e.continuous.measurable) hcov
    (fun q => ‖φ q‖ₑ ^ 2) (hφ.measurable.enorm.pow_const 2)
  apply hle.trans_eq
  rw [matrixHaarMeasure, setLIntegral_map (f := fun x => ‖φ (point F n x)‖ₑ ^ 2)
    (g := ⇑(GeneralLinearGroupPoints.adelicHomeomorph F n)) ht
    ((hφ.comp (continuous_point F n)).measurable.enorm.pow_const 2)
    (map_continuous (GeneralLinearGroupPoints.adelicHomeomorph F n)).measurable]
  refine lintegral_congr fun x => ?_
  simp only [point_adelicHomeomorph]
  rfl

/-- Square integrability on one rational covering set gives band `L²` membership. -/
theorem memLp_band_of_continuous (φ : Quotient F n → ℝ) (hφ : Continuous φ)
    (t : Set (AdelicGL F n)) (ht : MeasurableSet t)
    (hcover : ∀ x : AdelicGL F n,
      1 ≤ ((AdelicBlockDeterminantCharacter.determinantNorm F n x : ℝ≥0) : ℝ) ∧
        ((AdelicBlockDeterminantCharacter.determinantNorm F n x : ℝ≥0) : ℝ) ≤ 2 →
      ∃ γr : RationalGL F n, AdelicGL.rational F n γr * x ∈ t)
    (hfin : ∫⁻ x in t, ‖φ (point F n x)‖ₑ ^ 2 ∂matrixHaarMeasure F n < ∞) :
    MemLp φ 2 ((quotientHaarMeasure F n).restrict (band F n)) := by
  apply (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)
    hφ.aestronglyMeasurable).mpr
  simpa only [ENNReal.toReal_ofNat, ENNReal.rpow_two] using
    (lintegral_band_le_cover_of_continuous F n φ hφ t ht hcover).trans_lt hfin

end Cover

/-- The translation curve `s ↦ exp (s X)` at infinity, in the adelic matrix group. -/
abbrev curve (X : ArchimedeanGL.RealLieAlgebra F n) (s : ℝ) : AdelicGL F n :=
  AdelicGL.ofInfinite F n (ArchimedeanGL.infiniteOneParameter F n X s)

theorem continuous_curve (X : ArchimedeanGL.RealLieAlgebra F n) : Continuous (curve F n X) :=
  (map_continuous (AdelicGL.ofInfinite F n)).comp
    (ArchimedeanGL.continuous_infiniteOneParameter F n X)

theorem curve_zero (X : ArchimedeanGL.RealLieAlgebra F n) : curve F n X 0 = 1 := by
  rw [curve, ArchimedeanGL.infiniteOneParameter_zero, map_one]

variable (S : OperatorRealization F n)
local instance : AddCommGroup S.Space := Submodule.addCommGroup _

/-- Translating a realized quotient function along a continuous curve is jointly continuous. -/
theorem continuous_toQuotient_translate (h : S.Space) {c : ℝ → AdelicGL F n}
    (hc : Continuous c) :
    Continuous (fun p : Quotient F n × ℝ => toQuotient F n S h (translate F n (c p.2) p.1)) := by
  rw [← ((LeftCosetSpace.isOpenQuotientMap_mk _).prodMap
    IsOpenQuotientMap.id).continuous_comp_iff]
  have heq : ((fun p : Quotient F n × ℝ => toQuotient F n S h (translate F n (c p.2) p.1)) ∘
      Prod.map (LeftCosetSpace.mk (AdelicGroupPoints.rationalSubgroup F (matrixGroupScheme F n)))
        id) = fun p => evaluate F n (S.toContinuous h)
          (GeneralLinearGroupPoints.adelicHomeomorph F n p.1 * c p.2) := by
    funext p
    simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq,
      ← point_adelicHomeomorph, translate_point, toQuotient_point]
  rw [heq]
  exact (continuous_evaluate F n _).comp
    (((GeneralLinearGroupPoints.adelicHomeomorph F n).continuous.comp continuous_fst).mul
      (hc.comp continuous_snd))

/-- The largest value of a translated realized vector along `exp (s X)`, `|s| ≤ 1`. -/
def supNorm (X : ArchimedeanGL.RealLieAlgebra F n) (h : S.Space) (q : Quotient F n) : ℝ :=
  sSup ((fun s => ‖toQuotient F n S h (translate F n (curve F n X s) q)‖) ''
    Set.Icc (-1 : ℝ) 1)

theorem continuousOn_norm_translate (X : ArchimedeanGL.RealLieAlgebra F n) (h : S.Space)
    (q : Quotient F n) :
    Continuous (fun s => ‖toQuotient F n S h (translate F n (curve F n X s) q)‖) := by
  have h1 := (continuous_norm.comp (continuous_toQuotient_translate F n S h
    (continuous_curve F n X))).comp (Continuous.prodMk_right (X := Quotient F n) (Y := ℝ) q)
  exact h1

theorem continuous_supNorm (X : ArchimedeanGL.RealLieAlgebra F n) (h : S.Space) :
    Continuous (supNorm F n S X h) :=
  isCompact_Icc.continuous_sSup
    (continuous_norm.comp (continuous_toQuotient_translate F n S h (continuous_curve F n X)))

theorem norm_le_supNorm (X : ArchimedeanGL.RealLieAlgebra F n) (h : S.Space)
    (q : Quotient F n) {s : ℝ} (hs : s ∈ Set.Icc (-1 : ℝ) 1) :
    ‖toQuotient F n S h (translate F n (curve F n X s) q)‖ ≤ supNorm F n S X h q :=
  le_csSup (isCompact_Icc.bddAbove_image
    (continuousOn_norm_translate F n S X h q).continuousOn) (Set.mem_image_of_mem _ hs)

theorem supNorm_nonneg (X : ArchimedeanGL.RealLieAlgebra F n) (h : S.Space)
    (q : Quotient F n) : 0 ≤ supNorm F n S X h q :=
  (norm_nonneg _).trans (norm_le_supNorm F n S X h q (s := 0) ⟨by norm_num, by norm_num⟩)

theorem exists_supNorm_eq (X : ArchimedeanGL.RealLieAlgebra F n) (h : S.Space)
    (x : AdelicGL F n) :
    ∃ s ∈ Set.Icc (-1 : ℝ) 1, supNorm F n S X h (point F n x) =
      ‖evaluate F n (S.toContinuous h) (x * curve F n X s)‖ := by
  obtain ⟨s, hs, hseq⟩ := (isCompact_Icc.image
    (continuousOn_norm_translate F n S X h (point F n x))).sSup_mem
      ((Set.nonempty_Icc.mpr (by norm_num : (-1 : ℝ) ≤ 1)).image _)
  refine ⟨s, hs, ?_⟩
  rw [supNorm, ← hseq]
  simp only [translate_point, toQuotient_point]

/-- The supremum function of a cuspidal vector is square integrable on the band. -/
theorem memLp_supNorm [CompactSpace (AdeleQuotient F)] (hS : S.IsCuspidal)
    (X : ArchimedeanGL.RealLieAlgebra F n) (h : S.Space) :
    MemLp (supNorm F n S X h) 2 ((quotientHaarMeasure F n).restrict (band F n)) := by
  let : MeasurableSpace (AdelicGL F n) := borel _
  have : BorelSpace (AdelicGL F n) := ⟨rfl⟩
  obtain ⟨t, ht, hcover, hfin⟩ := S.exists_band_cover_uniform hS (lo := 1) (hi := 2) one_pos
    (curve F n X '' Set.Icc (-1) 1) (isCompact_Icc.image (continuous_curve F n X))
  refine memLp_band_of_continuous F n _ (continuous_supNorm F n S X h) t ht
    (fun x hx => hcover x hx.1 hx.2) ?_
  refine hfin (matrixHaarMeasure F n) h _ fun x => ?_
  obtain ⟨s, hs, heq⟩ := exists_supNorm_eq F n S X h x
  exact ⟨curve F n X s, Set.mem_image_of_mem _ hs, le_of_eq (by rw [heq, enorm_norm])⟩

end Langlands.Automorphic.OperatorDeterminantSlice

/-! ### Skew-adjointness of real Lie directions and the unitary form -/

namespace Langlands.Automorphic.OperatorDeterminantSlice

open Langlands.Global ContinuousRationalFunctions NumberField
open scoped CategoryTheory.MonObj

variable (F : Type uF) [Field F] [NumberField F] (n : ℕ)

local instance : IsAffine (matrixGroupScheme F n).X.left :=
  Langlands.GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)
local instance : Smooth (matrixGroupScheme F n).X.hom :=
  Langlands.GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of F)
local instance : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance : AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _

variable (S : OperatorRealization F n)
local instance : AddCommGroup S.Space := Submodule.addCommGroup _

/-- The pointwise Hermitian product of two band `L²` vectors is integrable. -/
theorem integrable_inner_toQuotient
    (hL2 : ∀ f : S.Space,
      MemLp (toQuotient F n S f) 2 ((quotientHaarMeasure F n).restrict (band F n)))
    (f g : S.Space) :
    Integrable (fun q => inner ℂ (toQuotient F n S f q) (toQuotient F n S g q))
      ((quotientHaarMeasure F n).restrict (band F n)) :=
  Integrable.mono' ((hL2 f).norm.integrable_mul (hL2 g).norm)
    ((toQuotient F n S f).continuous.inner (toQuotient F n S g).continuous).aestronglyMeasurable
    (ae_of_all _ fun _ => norm_inner_le_norm _ _)

set_option maxHeartbeats 1000000 in
/-- **Infinitesimal invariance.** Every actual real Lie direction is skew-adjoint for the
band form: differentiate the translation-invariant integral along `exp (s X)` at `s = 0`,
dominated by the band-square-integrable supremum functions. -/
theorem integral_inner_lieOperator_add [CompactSpace (AdeleQuotient F)] (hn : n ≠ 0)
    (hS : S.IsCuspidal) (χ : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ)
    (hχ : ∀ x, ‖(χ x : ℂ)‖ = 1) (hSχ : S.HasCentralCharacter χ)
    (hL2 : ∀ f : S.Space,
      MemLp (toQuotient F n S f) 2 ((quotientHaarMeasure F n).restrict (band F n)))
    (X : ArchimedeanGL.RealLieAlgebra F n) (f g : S.Space) :
    (∫ q, inner ℂ (toQuotient F n S (S.lieOperator X f) q) (toQuotient F n S g q)
        ∂(quotientHaarMeasure F n).restrict (band F n)) +
      ∫ q, inner ℂ (toQuotient F n S f q) (toQuotient F n S (S.lieOperator X g) q)
        ∂(quotientHaarMeasure F n).restrict (band F n) = 0 := by
  set ν := (quotientHaarMeasure F n).restrict (band F n) with hν
  set c := curve F n X with hc
  let G : ℝ → Quotient F n → ℂ := fun s q =>
    inner ℂ (toQuotient F n S f (translate F n (c s) q))
      (toQuotient F n S g (translate F n (c s) q))
  let G' : ℝ → Quotient F n → ℂ := fun s q =>
    inner ℂ (toQuotient F n S (S.lieOperator X f) (translate F n (c s) q))
        (toQuotient F n S g (translate F n (c s) q)) +
      inner ℂ (toQuotient F n S f (translate F n (c s) q))
        (toQuotient F n S (S.lieOperator X g) (translate F n (c s) q))
  have hpt : ∀ (h : S.Space) (q : Quotient F n) (s : ℝ),
      HasDerivAt (fun u => toQuotient F n S h (translate F n (c u) q))
        (toQuotient F n S (S.lieOperator X h) (translate F n (c s) q)) s := by
    intro h q s
    obtain ⟨x, rfl⟩ := point_surjective F n q
    simp only [hc, translate_point, toQuotient_point]
    exact S.hasDerivAt_evaluate_oneParameter X h x s
  have hdiff : ∀ q s, HasDerivAt (fun u => G u q) (G' s q) s := by
    intro q s
    have h := (hpt f q s).star.mul (hpt g q s)
    simp only [G, G', RCLike.inner_apply', starRingEnd_apply]
    exact h
  let B : Quotient F n → ℝ := fun q =>
    supNorm F n S X (S.lieOperator X f) q * supNorm F n S X g q +
      supNorm F n S X f q * supNorm F n S X (S.lieOperator X g) q
  have hbound : ∀ q, ∀ s ∈ Set.Ioo (-1 : ℝ) 1, ‖G' s q‖ ≤ B q := by
    intro q s hs
    have hs' := Set.Ioo_subset_Icc_self hs
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · exact (norm_inner_le_norm _ _).trans (mul_le_mul (norm_le_supNorm F n S X _ q hs')
        (norm_le_supNorm F n S X _ q hs') (norm_nonneg _) (supNorm_nonneg F n S X _ q))
    · exact (norm_inner_le_norm _ _).trans (mul_le_mul (norm_le_supNorm F n S X _ q hs')
        (norm_le_supNorm F n S X _ q hs') (norm_nonneg _) (supNorm_nonneg F n S X _ q))
  have hBint : Integrable B ν :=
    ((memLp_supNorm F n S hS X _).integrable_mul (memLp_supNorm F n S hS X g)).add
      ((memLp_supNorm F n S hS X f).integrable_mul (memLp_supNorm F n S hS X _))
  have htr0 : ∀ q, translate F n (c 0) q = q := fun q => by
    rw [hc, curve_zero, translate_one]
  have hG0 : G 0 = fun q => inner ℂ (toQuotient F n S f q) (toQuotient F n S g q) :=
    funext fun q => by simp only [G, htr0]
  have hG'0 : G' 0 = fun q =>
      inner ℂ (toQuotient F n S (S.lieOperator X f) q) (toQuotient F n S g q) +
        inner ℂ (toQuotient F n S f q) (toQuotient F n S (S.lieOperator X g) q) :=
    funext fun q => by simp only [G', htr0]
  have hcontG : ∀ s, Continuous (G s) := fun s =>
    ((toQuotient F n S f).continuous.comp (translate F n (c s)).continuous).inner
      ((toQuotient F n S g).continuous.comp (translate F n (c s)).continuous)
  have hint0 : Integrable (G 0) ν := by
    rw [hG0]
    exact integrable_inner_toQuotient F n S hL2 f g
  have hint'0 : Integrable (G' 0) ν := by
    rw [hG'0]
    exact (integrable_inner_toQuotient F n S hL2 _ g).add
      (integrable_inner_toQuotient F n S hL2 f _)
  have hJ := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := G) (F' := G')
    (x₀ := (0 : ℝ)) (Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1))
    (Eventually.of_forall fun s => (hcontG s).aestronglyMeasurable) hint0
    hint'0.aestronglyMeasurable (ae_of_all _ hbound) hBint
    (ae_of_all _ fun q s _ => hdiff q s)).2
  have hconst : (fun s => ∫ q, G s q ∂ν) =
      fun _ => ∫ q, inner ℂ (toQuotient F n S f q) (toQuotient F n S g q) ∂ν :=
    funext fun s => integral_inner_translate F n S hn (quotientHaarMeasure F n) χ hχ hSχ
      (fun a _ => measurePreserving_translate F n a) (c s) f g
  rw [hconst] at hJ
  have hzero := hJ.unique (hasDerivAt_const _ _)
  rw [hG'0, integral_add (integrable_inner_toQuotient F n S hL2 _ g)
    (integrable_inner_toQuotient F n S hL2 f _)] at hzero
  exact hzero

set_option maxHeartbeats 1000000 in
/-- The determinant-band form of a cuspidal realization with unitary central character,
as a positive form for the finite, compact and real Lie actions together. -/
def unitaryForm [CompactSpace (AdeleQuotient F)] (hn : n ≠ 0) (hS : S.IsCuspidal)
    (χ : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ)
    (hχ : ∀ x, ‖(χ x : ℂ)‖ = 1) (hSχ : S.HasCentralCharacter χ)
    (hL2 : ∀ f : S.Space,
      MemLp (toQuotient F n S f) 2 ((quotientHaarMeasure F n).restrict (band F n))) :
    S.UnitaryForm where
  finiteForm := finiteInvariantPositiveFormOfHaar F n S hn χ hχ hSχ hL2
  compact_invariant k f g := by
    change inner ℂ (toL2 F n S (quotientHaarMeasure F n) hL2 (S.compactRepresentation k f))
        (toL2 F n S (quotientHaarMeasure F n) hL2 (S.compactRepresentation k g)) =
      inner ℂ (toL2 F n S (quotientHaarMeasure F n) hL2 f)
        (toL2 F n S (quotientHaarMeasure F n) hL2 g)
    rw [inner_toL2, inner_toL2]
    simp only [toQuotient_compact]
    exact integral_inner_translate F n S hn (quotientHaarMeasure F n) χ hχ hSχ
      (fun a _ => measurePreserving_translate F n a) _ f g
  real_skew X f g := by
    change inner ℂ (toL2 F n S (quotientHaarMeasure F n) hL2 (S.lieOperator X f))
        (toL2 F n S (quotientHaarMeasure F n) hL2 g) +
      inner ℂ (toL2 F n S (quotientHaarMeasure F n) hL2 f)
        (toL2 F n S (quotientHaarMeasure F n) hL2 (S.lieOperator X g)) = 0
    rw [inner_toL2, inner_toL2]
    exact integral_inner_lieOperator_add F n S hn hS χ hχ hSχ hL2 X f g

/-- The unitary form is the band integral of the pointwise Hermitian product. -/
theorem unitaryForm_inner [CompactSpace (AdeleQuotient F)] (hn : n ≠ 0) (hS : S.IsCuspidal)
    (χ : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ)
    (hχ : ∀ x, ‖(χ x : ℂ)‖ = 1) (hSχ : S.HasCentralCharacter χ)
    (hL2 : ∀ f : S.Space,
      MemLp (toQuotient F n S f) 2 ((quotientHaarMeasure F n).restrict (band F n)))
    (f g : S.Space) :
    (unitaryForm F n S hn hS χ hχ hSχ hL2).inner f g =
      ∫ q, inner ℂ (toQuotient F n S f q) (toQuotient F n S g q)
        ∂(quotientHaarMeasure F n).restrict (band F n) :=
  inner_toL2 F n S (quotientHaarMeasure F n) hL2 f g

end Langlands.Automorphic.OperatorDeterminantSlice

/-! ### Unitarizability of cuspidal realizations with unitary central character -/

namespace Langlands.Automorphic.CuspidalOperatorRealization

open Langlands.Global

variable {F : Type uF} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] {r : ℕ}

/-- **Unitarizability.** An actual cuspidal realization with unitary central character
carries one positive definite Hermitian form invariant under the finite and compact
translations and infinitesimally invariant under every actual real Lie direction. -/
theorem isUnitarizable_of_hasUnitaryCentralCharacter (T : CuspidalOperatorRealization F r)
    (hT : Langlands.ClassField.Global.RelativeWeilGroup.HasUnitaryCentralCharacter T) :
    T.realization.IsUnitarizable := by
  obtain ⟨χ, hχ, hTχ⟩ := hT
  let : MeasurableSpace (AdelicGL F (r + 1)) := borel _
  have : BorelSpace (AdelicGL F (r + 1)) := ⟨rfl⟩
  obtain ⟨t, ht, hcover, hfinite⟩ :=
    T.realization.exists_band_cover T.cuspidal (lo := 1) (hi := 2) one_pos
  exact ⟨OperatorDeterminantSlice.unitaryForm F (r + 1) T.realization (Nat.succ_ne_zero r)
    T.cuspidal χ hχ hTχ fun f => OperatorDeterminantSlice.memLp_band_of_cover F (r + 1)
      T.realization t ht (fun x hx => hcover x hx.1 hx.2) f (hfinite _ f)⟩

end Langlands.Automorphic.CuspidalOperatorRealization
