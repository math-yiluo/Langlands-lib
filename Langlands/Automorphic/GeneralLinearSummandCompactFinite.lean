import Langlands.Automorphic.GroupSchemeQuotientRegularVectors
import Langlands.Automorphic.GeneralLinearSummandSmoothing
import Langlands.Automorphic.ArchimedeanFixedCompactDensity
import Langlands.Representation.CompactRepresentativeWeights
import Langlands.Global.ArchimedeanCompactCentralApproximationProof

/-! # Archimedean compact-finite smoothing of regular vectors in the quotient `L²` of `GL_n` -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory NumberField Set Topology Filter
open scoped CategoryTheory.MonObj Pointwise

set_option autoImplicit false

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.AdelicGroupPoints Langlands.Global.PositiveRealTorus
open Langlands.GroupScheme Langlands.Analysis.NormalizedAverage Langlands.FiniteVectors
open Langlands.CompactRepresentativeWeights Langlands.Automorphic.CuspidalFixedSmoothDensity

private local instance (F : Type u) [Field F] (n : ℕ) :
    IsAffine (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

private local instance (F : Type u) [Field F] (n : ℕ) :
    Smooth (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of F)

variable (F : Type u) [Field F] [NumberField F] (r : ℕ)

local notation "GLs" => GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)
local notation "K∞" => standardInfiniteCompact F (r + 1)
local notation "m" => GeneralLinearGroupPoints.adelicHomeomorph F (r + 1)

section Points

/-- The archimedean inclusion into the group-scheme adelic points, as a homomorphism. -/
def archimedeanAdelicHom : InfiniteAdelicGL F (r + 1) →* AdelicGroupPoints F GLs :=
  (m).symm.toMulEquiv.toMonoidHom.comp (AdelicGL.ofInfinite F (r + 1)).toMonoidHom

theorem archimedeanAdelicHom_apply (z : InfiniteAdelicGL F (r + 1)) :
    archimedeanAdelicHom F r z = archimedeanAdelicPoint F r z := rfl

theorem archimedeanAdelicPoint_mul (a b : InfiniteAdelicGL F (r + 1)) :
    archimedeanAdelicPoint F r (a * b) =
      archimedeanAdelicPoint F r a * archimedeanAdelicPoint F r b :=
  map_mul (archimedeanAdelicHom F r) a b

/-- Finite and archimedean adelic points commute. -/
theorem ofFinite_mul_archimedeanAdelicPoint (l : FiniteAdelicGroupPoints F GLs)
    (z : InfiniteAdelicGL F (r + 1)) :
    AdelicGroupPoints.ofFinite F GLs l * archimedeanAdelicPoint F r z =
      archimedeanAdelicPoint F r z * AdelicGroupPoints.ofFinite F GLs l := by
  apply (m).injective
  rw [map_mul, map_mul, GeneralLinearGroupPoints.adelicHomeomorph_ofFinite]
  change AdelicGL.ofFinite F (r + 1) _ * (m) ((m).symm (AdelicGL.ofInfinite F (r + 1) z)) =
    (m) ((m).symm (AdelicGL.ofInfinite F (r + 1) z)) * AdelicGL.ofFinite F (r + 1) _
  rw [ContinuousMulEquiv.apply_symm_apply, ofFinite_mul_ofInfinite]

/-- The standard archimedean compact subgroup as parameters in the adelic group. -/
def compactParameter : C(K∞, AdelicGroupPoints F GLs) :=
  (archimedeanAdelicPoint F r).comp ⟨Subtype.val, continuous_subtype_val⟩

theorem compactParameter_one : compactParameter F r 1 = 1 :=
  map_one (archimedeanAdelicHom F r)

/-- The archimedean points of `GL_n` form a second countable space. -/
theorem secondCountableTopology_infiniteAdelicGL :
    SecondCountableTopology (InfiniteAdelicGL F (r + 1)) :=
  (GeneralLinearGroupPoints.infiniteHomeomorph F (r + 1)).symm.toHomeomorph.isEmbedding
    |>.secondCountableTopology

end Points

variable (T : CommGroupScheme (Spec (CommRingCat.of F)))
  (i : T.toGrp ⟶ GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F))
  (hi : Function.Injective (characterRestrict i)) [(characterRestrict i).range.FiniteIndex]
  (I : Type u) [Fintype I]
  (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)
  [(Measure.haar : Measure (normOneSubgroup F
    (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)))).IsMulRightInvariant]

local notation "μQ" => positiveRationalQuotientHaarMeasure F GLs T i
local notation "ρ" => haarQuotientL2BoundedRightAction F GLs T i hi I e hc

/-- The restriction of the quotient right action to the standard archimedean compact
subgroup, as an algebraic representation. -/
def compactAction : Representation ℂ K∞ (Lp ℂ 2 μQ) :=
  (ContinuousLinearMap.toLinearMapRingHom.toMonoidHom.comp ρ).comp
    ((archimedeanAdelicHom F r).comp (standardInfiniteCompact F (r + 1)).subtype)

theorem compactAction_apply (k : K∞) (φ : Lp ℂ 2 μQ) :
    compactAction F r T i hi I e hc k φ = ρ (compactParameter F r k) φ := rfl

/-- The quotient right translation as a linear isometry. -/
def rightIsometry (g : AdelicGroupPoints F GLs) : Lp ℂ 2 μQ →ₗᵢ[ℂ] Lp ℂ 2 μQ :=
  ⟨(ρ g).toLinearMap, norm_haarQuotientL2BoundedRightAction F GLs T i hi I e hc g⟩

theorem rightIsometry_apply (g : AdelicGroupPoints F GLs) (φ : Lp ℂ 2 μQ) :
    rightIsometry F r T i hi I e hc g φ = ρ g φ := rfl

/-- The quotient right action of a product. -/
theorem rightAction_mul_apply (a b : AdelicGroupPoints F GLs) (φ : Lp ℂ 2 μQ) :
    ρ (a * b) φ = ρ a (ρ b φ) := by
  rw [map_mul]
  rfl

/-- Right translation commutes with Bochner integration. -/
theorem integral_rightTranslate {Y : Type*} [MeasurableSpace Y] (ν : Measure Y)
    (g : AdelicGroupPoints F GLs) (f : Y → Lp ℂ 2 μQ) :
    ρ g (∫ y, f y ∂ν) = ∫ y, ρ g (f y) ∂ν :=
  ((rightIsometry F r T i hi I e hc g).integral_comp_comm f).symm

section CompactAverage

variable [MeasurableSpace (standardInfiniteCompact F (r + 1))]
  [BorelSpace (standardInfiniteCompact F (r + 1))]

local notation "μK" => Langlands.Analysis.compactProbabilityHaar (standardInfiniteCompact F (r + 1))

theorem integrable_compactAverage (u : Lp ℂ 2 μQ) (a : C(K∞, ℂ)) :
    Integrable (fun k => a k • ρ (compactParameter F r k) u) μK :=
  (a.continuous.smul ((continuous_orbit F GLs T i hi I e hc u).comp
    (compactParameter F r).continuous)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Averages of one vector over the standard compact subgroup against continuous weights. -/
def compactAverage (u : Lp ℂ 2 μQ) : C(K∞, ℂ) →ₗ[ℂ] Lp ℂ 2 μQ where
  toFun a := ∫ k, a k • ρ (compactParameter F r k) u ∂μK
  map_add' a b := by
    simp only [ContinuousMap.add_apply, add_smul]
    exact integral_add (integrable_compactAverage F r T i hi I e hc u a)
      (integrable_compactAverage F r T i hi I e hc u b)
  map_smul' c a := by
    simp only [ContinuousMap.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply]
    exact integral_smul c _

theorem compactAverage_apply (u : Lp ℂ 2 μQ) (a : C(K∞, ℂ)) :
    compactAverage F r T i hi I e hc u a = ∫ k, a k • ρ (compactParameter F r k) u ∂μK := rfl

/-- Translating an average by a compact element is the average against the left translate of
the weight. -/
theorem compactAction_compactAverage (u : Lp ℂ 2 μQ) (a : C(K∞, ℂ)) (k : K∞) :
    compactAction F r T i hi I e hc k (compactAverage F r T i hi I e hc u a) =
      compactAverage F r T i hi I e hc u (leftRegular k a) := by
  rw [compactAction_apply, compactAverage_apply, compactAverage_apply,
    integral_rightTranslate F r T i hi I e hc]
  let f : K∞ → Lp ℂ 2 μQ := fun k' => leftRegular k a k' • ρ (compactParameter F r k') u
  rw [← (integral_mul_left_eq_self f k : (∫ k', f (k * k') ∂μK) = ∫ k', f k' ∂μK)]
  congr 1
  funext k'
  simp only [f, leftRegular_apply, inv_mul_cancel_left, map_smul]
  congr 1
  change ρ (compactParameter F r k) (ρ (compactParameter F r k') u) =
    ρ (archimedeanAdelicPoint F r (k * k').val) u
  rw [Subgroup.coe_mul, archimedeanAdelicPoint_mul, map_mul]
  rfl

/-- The average map is an intertwiner from the left regular action on weights. -/
def compactAverageIntertwiner (u : Lp ℂ 2 μQ) :
    (leftRegular (K := K∞)).IntertwiningMap (compactAction F r T i hi I e hc) where
  toLinearMap := compactAverage F r T i hi I e hc u
  isIntertwining' k := by
    apply LinearMap.ext
    intro a
    exact (compactAction_compactAverage F r T i hi I e hc u a k).symm

theorem isFiniteVector_compactAverage (u : Lp ℂ 2 μQ) {a : C(K∞, ℂ)} (ha : a ∈ finiteWeights) :
    IsFiniteVector (compactAction F r T i hi I e hc) (compactAverage F r T i hi I e hc u a) :=
  (show IsFiniteVector leftRegular a from ha).map (compactAverageIntertwiner F r T i hi I e hc u)

/-- Averaging a regular vector against a continuous weight on the standard compact subgroup keeps
it regular, as long as the average is nonzero. -/
theorem isRegularVector_compactAverage [SecondCountableTopology (standardInfiniteCompact F (r + 1))]
    (A : Submodule ℂ (Lp ℂ 2 μQ))
    (hAc : IsClosed (A : Set (Lp ℂ 2 μQ))) (hAinv : ∀ g, ∀ φ ∈ A, ρ g φ ∈ A)
    {L : Subgroup (FiniteAdelicGroupPoints F GLs)} {u : Lp ℂ 2 μQ}
    (hu : IsRegularVector F GLs T i hi I e hc A L u) (a : C(K∞, ℂ))
    (hne : compactAverage F r T i hi I e hc u a ≠ 0) :
    IsRegularVector F GLs T i hi I e hc A L (compactAverage F r T i hi I e hc u a) := by
  obtain ⟨h, S, C, hS, hC, hae, hMB, hL⟩ := hu.rep
  obtain ⟨-, hae'⟩ := groupSchemeQuotientL2IntegratedRepresentative F GLs T i hi I e hc μK
    (compactParameter F r) a (HasCompactSupport.of_compactSpace _) u h hae
  refine ⟨integral_mem_of_isClosed A hAc (integrable_compactAverage F r T i hi I e hc u a)
      fun k => A.smul_mem _ (hAinv _ u hu.mem), hne,
    weightedQuotientOrbitIntegral F GLs T i μK (compactParameter F r) a
      (HasCompactSupport.of_compactSpace _) h, _, _,
    isCompact_conjugateSet F GLs ((HasCompactSupport.of_compactSpace a).isCompact.image
      (compactParameter F r).continuous) hS,
    mul_nonneg hC (sq_nonneg _), hae',
    quotientMassBound_weightedQuotientOrbitIntegral F GLs T i hi I e hc μK _ _ _ h hS hC hMB,
    hL.weightedQuotientOrbitIntegral F GLs T i μK _ _ _ fun l _ k =>
      ofFinite_mul_archimedeanAdelicPoint F r l k.val⟩


/-- **A nonzero compact-finite average.** A nonzero vector has a nonzero average against some
continuous weight whose left translates span a finite-dimensional space (`finiteWeights`): such
weights approximate a normalized bump near the identity uniformly. -/
theorem exists_finiteWeight_compactAverage_ne_zero {u : Lp ℂ 2 μQ} (hu : u ≠ 0) :
    ∃ a ∈ (finiteWeights : StarSubalgebra ℂ C(K∞, ℂ)),
      compactAverage F r T i hi I e hc u a ≠ 0 := by
  classical
  have hupos : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hpos : 0 < ‖u‖ / 4 := by positivity
  have horb : Continuous fun k : K∞ => ρ (compactParameter F r k) u :=
    (continuous_orbit F GLs T i hi I e hc u).comp (compactParameter F r).continuous
  have hU : {k : K∞ | ‖ρ (compactParameter F r k) u - u‖ < ‖u‖ / 4} ∈ 𝓝 (1 : K∞) := by
    apply ((horb.sub continuous_const).norm.isOpen_preimage _ isOpen_Iio).mem_nhds
    change ‖ρ (compactParameter F r 1) u - u‖ < _
    rw [compactParameter_one, map_one, one_apply_eq_self, sub_self, norm_zero]
    exact hpos
  obtain ⟨a₀, -, ha₀s, ha₀1, ha₀n⟩ := exists_normalized_bump μK 1 hU
  have hdense := dense_finiteWeights (compactComplexRepresentation F (r + 1))
    continuous_compactComplexRepresentation_orbit compactComplexRepresentation_injective
  obtain ⟨a, hball, ha⟩ := Metric.dense_iff.mp hdense a₀ (1 / 4) (by norm_num)
  refine ⟨a, ha, fun h0 => ?_⟩
  have h1 : ‖compactAverage F r T i hi I e hc u a₀ - u‖ ≤ ‖u‖ / 4 :=
    norm_integral_smul_sub_le a₀ (fun k => ρ (compactParameter F r k) u) u
      (integrable_compactAverage F r T i hi I e hc u a₀)
      (a₀.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      ha₀1 ha₀n fun k hk => (ha₀s k hk).le
  have hd : ‖a - a₀‖ ≤ 1 / 4 := by
    rw [← dist_eq_norm]
    exact (Metric.mem_ball.mp hball).le
  have h2 : ‖compactAverage F r T i hi I e hc u a - compactAverage F r T i hi I e hc u a₀‖ ≤
      ‖u‖ / 4 := by
    rw [← map_sub, compactAverage_apply]
    calc ‖∫ k, (a - a₀) k • ρ (compactParameter F r k) u ∂μK‖
        ≤ ∫ _k, ‖a - a₀‖ * ‖u‖ ∂μK :=
          norm_integral_le_of_norm_le (integrable_const _) (Eventually.of_forall fun k => by
            rw [norm_smul, norm_haarQuotientL2BoundedRightAction]
            exact mul_le_mul_of_nonneg_right ((a - a₀).norm_coe_le_norm k) (norm_nonneg _))
      _ = ‖a - a₀‖ * ‖u‖ := by simp only [integral_const, probReal_univ, one_smul]
      _ ≤ 1 / 4 * ‖u‖ := mul_le_mul_of_nonneg_right hd (norm_nonneg _)
      _ = ‖u‖ / 4 := by ring
  have h3 : ‖u‖ ≤ ‖u‖ / 2 := by
    calc ‖u‖ = ‖compactAverage F r T i hi I e hc u a - u‖ := by rw [h0, zero_sub, norm_neg]
      _ ≤ ‖compactAverage F r T i hi I e hc u a - compactAverage F r T i hi I e hc u a₀‖ +
          ‖compactAverage F r T i hi I e hc u a₀ - u‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ ‖u‖ / 2 := by linarith
  linarith

end CompactAverage

section Smoothing

variable [MeasurableSpace (InfiniteAdelicGL F (r + 1))] [BorelSpace (InfiniteAdelicGL F (r + 1))]
  (ν : Measure (InfiniteAdelicGL F (r + 1))) [ν.IsHaarMeasure]
  [SecondCountableTopology (InfiniteAdelicGL F (r + 1))]

omit [(Measure.haar : Measure (normOneSubgroup F
    (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)))).IsMulRightInvariant]
  [MeasurableSpace (InfiniteAdelicGL F (r + 1))] [BorelSpace (InfiniteAdelicGL F (r + 1))]
  [SecondCountableTopology (InfiniteAdelicGL F (r + 1))] in
theorem smoothingWeight_one_apply (κ : ArchimedeanGL.SmoothCompactKernel F (r + 1))
    (z : InfiniteAdelicGL F (r + 1)) : smoothingWeight F r 1 κ z = κ.val.val z⁻¹ := by
  change (ArchimedeanGL.envelopingAction F (r + 1) 1 κ.val).val z⁻¹ = _
  rw [map_one, Module.End.one_apply]

omit [(Measure.haar : Measure (normOneSubgroup F
    (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)))).IsMulRightInvariant]
  [MeasurableSpace (InfiniteAdelicGL F (r + 1))] [BorelSpace (InfiniteAdelicGL F (r + 1))]
  [SecondCountableTopology (InfiniteAdelicGL F (r + 1))] in
theorem smoothingWeight_conj (κ : ArchimedeanGL.SmoothCompactKernel F (r + 1))
    (hκ : ∀ (k : K∞) (x : InfiniteAdelicGL F (r + 1)),
      κ.val.val (k.val⁻¹ * x * k.val) = κ.val.val x) (k : K∞) (z : InfiniteAdelicGL F (r + 1)) :
    smoothingWeight F r 1 κ (k.val⁻¹ * (z * k.val)) = smoothingWeight F r 1 κ z := by
  have hinv : (k.val⁻¹ * (z * k.val))⁻¹ = k.val⁻¹ * z⁻¹ * k.val := by
    rw [mul_inv_rev, mul_inv_rev, inv_inv]
  rw [smoothingWeight_one_apply, smoothingWeight_one_apply, hinv, hκ k z⁻¹]

omit [(Measure.haar : Measure (normOneSubgroup F
    (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)))).IsMulRightInvariant]
  [MeasurableSpace (InfiniteAdelicGL F (r + 1))] [BorelSpace (InfiniteAdelicGL F (r + 1))]
  [SecondCountableTopology (InfiniteAdelicGL F (r + 1))] in
theorem archimedeanAdelicPoint_conj (k : K∞) (z : InfiniteAdelicGL F (r + 1)) :
    archimedeanAdelicPoint F r (k.val * (k.val⁻¹ * (z * k.val))) =
      archimedeanAdelicPoint F r z * compactParameter F r k := by
  rw [mul_inv_cancel_left, archimedeanAdelicPoint_mul]
  rfl

omit [(Measure.haar : Measure (normOneSubgroup F
    (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)))).IsMulRightInvariant]
  [MeasurableSpace (InfiniteAdelicGL F (r + 1))] [BorelSpace (InfiniteAdelicGL F (r + 1))]
  [SecondCountableTopology (InfiniteAdelicGL F (r + 1))] in
theorem archimedeanAdelicPoint_mul_left (k : K∞) (z : InfiniteAdelicGL F (r + 1)) :
    archimedeanAdelicPoint F r (k.val * z) =
      compactParameter F r k * archimedeanAdelicPoint F r z :=
  archimedeanAdelicPoint_mul F r k.val z

omit [SecondCountableTopology (InfiniteAdelicGL F (r + 1))] in
theorem integrable_smoothing (D : ArchimedeanGL.EnvelopingAlgebra F (r + 1))
    (κ : ArchimedeanGL.SmoothCompactKernel F (r + 1)) (u : Lp ℂ 2 μQ) :
    Integrable (fun z => smoothingWeight F r D κ z • ρ (archimedeanAdelicPoint F r z) u) ν :=
  ((smoothingWeight F r D κ).continuous.smul ((continuous_orbit F GLs T i hi I e hc u).comp
    (archimedeanAdelicPoint F r).continuous)).integrable_of_hasCompactSupport
    (smoothingWeight_hasCompactSupport F r D κ).smul_right

omit [SecondCountableTopology (InfiniteAdelicGL F (r + 1))] in
/-- The smoothing of all vectors by one kernel, as a linear map. -/
def smoothingLinear (κ : ArchimedeanGL.SmoothCompactKernel F (r + 1)) :
    Lp ℂ 2 μQ →ₗ[ℂ] Lp ℂ 2 μQ where
  toFun u := smoothedClass F r T i ν hi I e hc 1 κ u
  map_add' u v := by
    simp only [smoothedClass, map_add, smul_add]
    exact integral_add (integrable_smoothing F r T i hi I e hc ν 1 κ u)
      (integrable_smoothing F r T i hi I e hc ν 1 κ v)
  map_smul' c u := by
    simp only [smoothedClass, map_smul, RingHom.id_apply]
    rw [← integral_smul]
    congr 1
    funext z
    rw [smul_comm]

omit [SecondCountableTopology (InfiniteAdelicGL F (r + 1))] in
/-- **Conjugation-invariant smoothing commutes with the compact action.** If the kernel is
invariant under conjugation by the standard compact subgroup and the Haar measure is invariant
under right translation by it, smoothing commutes with the action of the compact subgroup. -/
theorem smoothedClass_compactAction (κ : ArchimedeanGL.SmoothCompactKernel F (r + 1))
    (hκ : ∀ (k : K∞) (x : InfiniteAdelicGL F (r + 1)),
      κ.val.val (k.val⁻¹ * x * k.val) = κ.val.val x)
    (hν : ∀ k : K∞, Measure.map (· * k.val) ν = ν) (k : K∞) (u : Lp ℂ 2 μQ) :
    smoothedClass F r T i ν hi I e hc 1 κ (compactAction F r T i hi I e hc k u) =
      compactAction F r T i hi I e hc k (smoothedClass F r T i ν hi I e hc 1 κ u) := by
  rw [compactAction_apply, compactAction_apply, smoothedClass, smoothedClass,
    integral_rightTranslate F r T i hi I e hc]
  have hR : MeasurePreserving (MeasurableEquiv.mulRight k.val) ν ν :=
    ⟨(MeasurableEquiv.mulRight k.val).measurable, by
      rw [MeasurableEquiv.coe_mulRight]
      exact hν k⟩
  have h1 := hR.integral_comp' (fun y => smoothingWeight F r 1 κ (k.val⁻¹ * y) •
    ρ (archimedeanAdelicPoint F r (k.val * (k.val⁻¹ * y))) u)
  simp only [MeasurableEquiv.coe_mulRight] at h1
  rw [integral_mul_left_eq_self (fun y => smoothingWeight F r 1 κ y •
    ρ (archimedeanAdelicPoint F r (k.val * y)) u) k.val⁻¹] at h1
  have h2 (z : InfiniteAdelicGL F (r + 1)) :
      smoothingWeight F r 1 κ (k.val⁻¹ * (z * k.val)) •
        ρ (archimedeanAdelicPoint F r (k.val * (k.val⁻¹ * (z * k.val)))) u =
      smoothingWeight F r 1 κ z • ρ (archimedeanAdelicPoint F r z)
        (ρ (compactParameter F r k) u) := by
    rw [smoothingWeight_conj F r κ hκ k z, archimedeanAdelicPoint_conj F r k z,
      rightAction_mul_apply F r T i hi I e hc]
  have h3 (z : InfiniteAdelicGL F (r + 1)) :
      smoothingWeight F r 1 κ z • ρ (archimedeanAdelicPoint F r (k.val * z)) u =
        ρ (compactParameter F r k)
          (smoothingWeight F r 1 κ z • ρ (archimedeanAdelicPoint F r z) u) := by
    refine (congrArg (fun g : AdelicGroupPoints F GLs => smoothingWeight F r 1 κ z • ρ g u)
      (archimedeanAdelicPoint_mul_left F r k z)).trans ?_
    refine (congrArg (fun φ : Lp ℂ 2 μQ => smoothingWeight F r 1 κ z • φ)
      (rightAction_mul_apply F r T i hi I e hc _ _ u)).trans ?_
    exact ((ρ (compactParameter F r k)).map_smul _ _).symm
  simp only [h2] at h1
  simp only [h3] at h1
  exact h1

omit [SecondCountableTopology (InfiniteAdelicGL F (r + 1))] in
/-- Smoothing by a kernel invariant under conjugation by the standard compact subgroup, as an
intertwiner of the compact action. -/
def smoothingIntertwiner (κ : ArchimedeanGL.SmoothCompactKernel F (r + 1))
    (hκ : ∀ (k : K∞) (x : InfiniteAdelicGL F (r + 1)),
      κ.val.val (k.val⁻¹ * x * k.val) = κ.val.val x)
    (hν : ∀ k : K∞, Measure.map (· * k.val) ν = ν) :
    (compactAction F r T i hi I e hc).IntertwiningMap (compactAction F r T i hi I e hc) where
  toLinearMap := smoothingLinear F r T i hi I e hc ν κ
  isIntertwining' k := by
    apply LinearMap.ext
    intro u
    exact smoothedClass_compactAction F r T i hi I e hc ν κ hκ hν k u

omit [SecondCountableTopology (InfiniteAdelicGL F (r + 1))] in
/-- Smoothing by a kernel invariant under conjugation by the standard compact subgroup preserves
`K∞`-finiteness: a finite-dimensional orbit span under the compact action. -/
theorem isFiniteVector_smoothedClass (κ : ArchimedeanGL.SmoothCompactKernel F (r + 1))
    (hκ : ∀ (k : K∞) (x : InfiniteAdelicGL F (r + 1)),
      κ.val.val (k.val⁻¹ * x * k.val) = κ.val.val x)
    (hν : ∀ k : K∞, Measure.map (· * k.val) ν = ν) {u : Lp ℂ 2 μQ}
    (hu : IsFiniteVector (compactAction F r T i hi I e hc) u) :
    IsFiniteVector (compactAction F r T i hi I e hc) (smoothedClass F r T i ν hi I e hc 1 κ u) :=
  hu.map (smoothingIntertwiner F r T i hi I e hc ν κ hκ hν)

omit [SecondCountableTopology (InfiniteAdelicGL F (r + 1))] in
/-- **A nonzero conjugation-invariant smoothing.** A nonzero vector has a nonzero smoothing by a
smooth compactly supported kernel invariant under conjugation by the standard compact
subgroup. -/
theorem exists_smoothedClass_ne_zero {u : Lp ℂ 2 μQ} (hu : u ≠ 0) :
    ∃ κ : ArchimedeanGL.SmoothCompactKernel F (r + 1),
      (∀ (k : K∞) (x : InfiniteAdelicGL F (r + 1)),
        κ.val.val (k.val⁻¹ * x * k.val) = κ.val.val x) ∧
      smoothedClass F r T i ν hi I e hc 1 κ u ≠ 0 := by
  have hpos : 0 < ‖u‖ / 2 := half_pos (norm_pos_iff.mpr hu)
  have horb : Continuous fun y : InfiniteAdelicGL F (r + 1) =>
      ρ (archimedeanAdelicPoint F r y⁻¹) u :=
    (continuous_orbit F GLs T i hi I e hc u).comp
      ((archimedeanAdelicPoint F r).continuous.comp continuous_inv)
  have hU : {y : InfiniteAdelicGL F (r + 1) | ‖ρ (archimedeanAdelicPoint F r y⁻¹) u - u‖ <
      ‖u‖ / 2} ∈ 𝓝 1 := by
    apply ((horb.sub continuous_const).norm.isOpen_preimage _ isOpen_Iio).mem_nhds
    change ‖ρ (archimedeanAdelicHom F r 1⁻¹) u - u‖ < _
    rw [inv_one, map_one, map_one, one_apply_eq_self, sub_self, norm_zero]
    exact hpos
  obtain ⟨κ, hsupp, hreal, -, hint, hconj, -⟩ :=
    ArchimedeanGL.compactCentralConvolutionApproximation F (r + 1) ν 0 univ univ_mem _ hU
  refine ⟨κ, hconj, ?_⟩
  have hw (z : InfiniteAdelicGL F (r + 1)) :
      smoothingWeight F r 1 κ z = ((κ.val.val z⁻¹).re : ℂ) := by
    rw [smoothingWeight_one_apply]
    exact Complex.ext (by simp) (by simp [(hreal z⁻¹).2])
  have hwI : Integrable (fun z => smoothingWeight F r 1 κ z) ν :=
    (smoothingWeight F r 1 κ).continuous.integrable_of_hasCompactSupport
      (smoothingWeight_hasCompactSupport F r 1 κ)
  have h1 : (∫ z, smoothingWeight F r 1 κ z ∂ν) = 1 := by
    simp only [smoothingWeight_one_apply]
    exact hint
  apply integral_smul_ne_zero (fun z => smoothingWeight F r 1 κ z)
    (fun z => ρ (archimedeanAdelicPoint F r z) u) u hu
    (integrable_smoothing F r T i hi I e hc ν 1 κ u) hwI h1
  · have hn (z : InfiniteAdelicGL F (r + 1)) :
        ‖smoothingWeight F r 1 κ z‖ = (smoothingWeight F r 1 κ z).re := by
      rw [hw, Complex.norm_real, Complex.ofReal_re, Real.norm_eq_abs,
        abs_of_nonneg (hreal z⁻¹).1]
    simp_rw [hn]
    have hre := integral_re hwI
    simp only [RCLike.re_to_complex] at hre
    rw [hre, h1, Complex.one_re]
  · intro z hz
    have hz' : z⁻¹ ∈ tsupport κ.val.val := by
      apply subset_tsupport
      rw [smoothingWeight_one_apply] at hz
      exact hz
    have := hsupp hz'
    simp only [Set.mem_ofPred_eq, inv_inv] at this
    exact this.le

end Smoothing

/-- **A compact-finite regular vector.** A regular vector of a closed invariant subspace,
invariant under a subgroup `L` of the finite adelic points, gives a regular vector, invariant
under the same `L`, whose orbit under the standard archimedean compact subgroup spans a
finite-dimensional space. -/
theorem exists_isRegularVector_compactFinite (A : Submodule ℂ (Lp ℂ 2 μQ))
    (hAc : IsClosed (A : Set (Lp ℂ 2 μQ))) (hAinv : ∀ g, ∀ φ ∈ A, ρ g φ ∈ A)
    {L : Subgroup (FiniteAdelicGroupPoints F GLs)} {u : Lp ℂ 2 μQ}
    (hu : IsRegularVector F GLs T i hi I e hc A L u) :
    ∃ v, IsRegularVector F GLs T i hi I e hc A L v ∧
      IsFiniteVector (compactAction F r T i hi I e hc) v := by
  let : MeasurableSpace K∞ := borel _
  have : BorelSpace K∞ := ⟨rfl⟩
  have := secondCountableTopology_infiniteAdelicGL F r
  have : SecondCountableTopology K∞ :=
    TopologicalSpace.secondCountableTopology_induced _ (InfiniteAdelicGL F (r + 1))
      (fun k : K∞ => (k : InfiniteAdelicGL F (r + 1)))
  obtain ⟨a, ha, hne⟩ := exists_finiteWeight_compactAverage_ne_zero F r T i hi I e hc hu.ne_zero
  exact ⟨_, isRegularVector_compactAverage F r T i hi I e hc A hAc hAinv hu a hne,
    isFiniteVector_compactAverage F r T i hi I e hc u ha⟩

end Langlands.Automorphic.GroupSchemeFunctions
