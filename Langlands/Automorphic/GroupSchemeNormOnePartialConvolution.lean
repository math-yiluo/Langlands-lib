import Langlands.Automorphic.GroupSchemeCuspidalConvolutionCompact
import Langlands.Global.AdelicQuotientConvolutionGrowth
import Langlands.Global.AdelicGroupPolish

/-! # Norm-one partial convolutions of positive-quotient `L²` classes -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory Set Filter Topology
open scoped CategoryTheory.MonObj CompactlySupported Pointwise InnerProductSpace

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global AdelicGroupPoints PositiveRealTorus RepresentationGrowth InfiniteAdelicGroupPoints
  Langlands.GroupScheme

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)

local notation "A" => AdelicGroupPoints F G
local notation "A¹" => normOneSubgroup F G
local notation "T⁺" => intrinsicSubgroup F T
local notation "Γ" => positiveRationalSubgroup F G T i
local notation "Q" => PositiveRationalQuotient F G T i
local notation "dq" => positiveRationalQuotientHaarMeasure F G T i
local notation "dg" => (Measure.haar : Measure A)
local notation "dn" => (Measure.haar : Measure (normOneSubgroup F G))
local notation "q" => LeftCosetSpace.mk Γ
local notation "V" => Lp ℂ 2 dq
local notation "pp" => positivePointMap F G T i

/-- The partial convolution `y ↦ ∫_{G(𝔸)¹} κ(n⁻¹ y) v(n) dn` over the norm-one subgroup, of a
kernel `κ` on `G(𝔸)` against an `L²` class `v` on the positive rational quotient, evaluated at
the chosen representative of `v`. -/
def normOnePartialConvolution (κ : A → ℂ) (v : V) (y : A) : ℂ :=
  ∫ n : normOneSubgroup F G, κ ((n : A)⁻¹ * y) * v (q n.val) ∂dn

omit [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
theorem positivePointMap_mem_positiveRationalSubgroup (a : T⁺) : pp a ∈ Γ :=
  imageSubgroup_le_positiveRationalSubgroup F G T i ⟨a.val, a.property, rfl⟩

omit [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
theorem mk_positivePointMap_mul (a : T⁺) (x : A) : q (pp a * x) = q x :=
  LeftCosetSpace.mk_subgroup_mul Γ ⟨pp a, positivePointMap_mem_positiveRationalSubgroup T i a⟩ x

variable (hi : Function.Injective (characterRestrict i)) [(characterRestrict i).range.FiniteIndex]
  (I : Type u) [Fintype I] (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)

local notation "ν" => normalizedPositiveHaarMeasure F G T i hi I e hc
local notation "π₀" => positiveFactor F G T i hi I e
local notation "π₁" => normOneFactor F G T i hi I e
local notation "dΓ" => positiveRationalSubgroupHaarMeasure F G T i hi I e hc

/-- A continuous compactly supported nonnegative function on the positive torus with total
normalized Haar integral one. -/
theorem exists_positiveTorusBump :
    ∃ β : T⁺ → ℝ, Continuous β ∧ HasCompactSupport β ∧ (∀ a, 0 ≤ β a) ∧ ∫ a, β a ∂ν = 1 := by
  let := positiveIsTopologicalGroup F T I e
  let := positiveLocallyCompactSpace F T I e
  let := normalizedPositiveHaarMeasure_isHaarMeasure F G T i hi I e hc
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : T⁺)
  obtain ⟨f, hf1, -, hfc, hf01⟩ :=
    exists_continuous_one_zero_of_isCompact hK isClosed_empty (disjoint_empty K)
  have hpos : 0 < ∫ a, f a ∂ν := by
    refine f.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hfc
      (fun a => (hf01 a).1) (x := 1) ?_
    rw [hf1 (mem_of_mem_nhds hK1)]
    exact one_ne_zero
  refine ⟨fun a => (∫ a, f a ∂ν)⁻¹ * f a, continuous_const.mul f.continuous,
    hfc.mul_left, fun a => mul_nonneg (inv_nonneg.mpr hpos.le) (hf01 a).1, ?_⟩
  rw [integral_const_mul, inv_mul_cancel₀ hpos.ne']

/-- The full-group kernel attached to a kernel `κ`, a positive-torus weight `β` and a positive
coordinate `c`: `w ↦ β(w₊) κ(c · (w¹)⁻¹)`, where `w = w₊ w¹` is the positive/norm-one
decomposition. -/
def normOnePositiveKernel (β : T⁺ → ℝ) (κ : A → ℂ) (c : T⁺) (w : A) : ℂ :=
  (β (π₀ w) : ℂ) * κ (pp c * ((π₁ w : A))⁻¹)

omit [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
theorem normOneFactor_positivePointMap_mul (a : T⁺) (n : A¹) : π₁ (pp a * n) = n := by
  apply Subtype.ext
  rw [normOneFactor_val, positiveFactor_mul_normOne, inv_mul_cancel_left]

omit [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
theorem normOnePositiveKernel_positivePointMap_mul (β : T⁺ → ℝ) (κ : A → ℂ) (c a : T⁺)
    (n : A¹) :
    normOnePositiveKernel T i hi I e β κ c (pp a * n) = (β a : ℂ) * κ (pp c * (n : A)⁻¹) := by
  rw [normOnePositiveKernel, positiveFactor_mul_normOne, normOneFactor_positivePointMap_mul]

omit [LocallyOfFiniteType G.X.hom] in
theorem continuous_normOnePositiveKernel {β : T⁺ → ℝ} {κ : A → ℂ} (hβ : Continuous β)
    (hκ : Continuous κ) (c : T⁺) : Continuous (normOnePositiveKernel T i hi I e β κ c) :=
  (Complex.continuous_ofReal.comp (hβ.comp (π₀).continuous)).mul
    (hκ.comp (continuous_const.mul
      (continuous_subtype_val.comp (continuous_normOneFactor F G T i hi I e)).inv))

/-- A common support bound for the kernels `normOnePositiveKernel β κ c`. -/
def normOnePositiveKernelSupport (β : T⁺ → ℝ) (κ : A → ℂ) : Set A :=
  pp '' tsupport β * ((tsupport κ)⁻¹ * pp '' (π₀ '' tsupport κ))

omit [LocallyOfFiniteType G.X.hom] in
theorem isCompact_normOnePositiveKernelSupport {β : T⁺ → ℝ} {κ : A → ℂ} (hβ : HasCompactSupport β)
    (hκ : HasCompactSupport κ) : IsCompact (normOnePositiveKernelSupport T i hi I e β κ) :=
  (hβ.isCompact.image (pp).continuous).mul
    (hκ.isCompact.inv.mul ((hκ.isCompact.image (π₀).continuous).image (pp).continuous))

omit [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
theorem support_normOnePositiveKernel_subset (β : T⁺ → ℝ) (κ : A → ℂ) (c : T⁺) :
    Function.support (normOnePositiveKernel T i hi I e β κ c) ⊆
      normOnePositiveKernelSupport T i hi I e β κ := by
  intro w hw
  have hw' : (β (π₀ w) : ℂ) ≠ 0 ∧ κ (pp c * ((π₁ w : A))⁻¹) ≠ 0 := by
    simpa only [Function.mem_support, normOnePositiveKernel, mul_ne_zero_iff] using hw
  set z := pp c * ((π₁ w : A))⁻¹ with hz
  have hβw : π₀ w ∈ tsupport β := subset_tsupport _ fun h => hw'.1 (by rw [h, Complex.ofReal_zero])
  have hκz : z ∈ tsupport κ := subset_tsupport _ hw'.2
  have hπz : π₀ z = c := by
    rw [hz, map_mul, map_inv, positiveFactor_positivePointMap, positiveFactor_normOne, inv_one,
      mul_one]
  have hw₁ : (π₁ w : A) = z⁻¹ * pp (π₀ z) := by
    rw [hπz, hz, mul_inv_rev, inv_inv, inv_mul_cancel_right]
  rw [← positivePointMap_mul_normOneFactor F G T i hi I e w, hw₁]
  exact Set.mul_mem_mul (Set.mem_image_of_mem _ hβw)
    (Set.mul_mem_mul (Set.inv_mem_inv.mpr hκz) (Set.mem_image_of_mem _ (Set.mem_image_of_mem _ hκz)))

omit [LocallyOfFiniteType G.X.hom] in
theorem tsupport_normOnePositiveKernel_subset {β : T⁺ → ℝ} {κ : A → ℂ} (hβ : HasCompactSupport β)
    (hκ : HasCompactSupport κ) (c : T⁺) :
    tsupport (normOnePositiveKernel T i hi I e β κ c) ⊆ normOnePositiveKernelSupport T i hi I e β κ :=
  closure_minimal (support_normOnePositiveKernel_subset T i hi I e β κ c)
    (isCompact_normOnePositiveKernelSupport T i hi I e hβ hκ).isClosed

omit [LocallyOfFiniteType G.X.hom] in
theorem hasCompactSupport_normOnePositiveKernel {β : T⁺ → ℝ} {κ : A → ℂ}
    (hβ : HasCompactSupport β) (hκ : HasCompactSupport κ) (c : T⁺) :
    HasCompactSupport (normOnePositiveKernel T i hi I e β κ c) :=
  (isCompact_normOnePositiveKernelSupport T i hi I e hβ hκ).of_isClosed_subset (isClosed_tsupport _)
    (tsupport_normOnePositiveKernel_subset T i hi I e hβ hκ c)

include hi e hc in
/-- The pullback of the chosen representative of an `L²` class to the norm-one subgroup is
strongly measurable. -/
theorem stronglyMeasurable_normOnePullback (v : V) :
    StronglyMeasurable (fun n : A¹ => v (q n.val)) := by
  let := positiveRationalQuotient_borelSpace F G T i hi I e hc
  exact (Lp.stronglyMeasurable v).comp_measurable
    ((LeftCosetSpace.continuous_mk Γ).comp continuous_subtype_val).measurable

variable [(Measure.haar : Measure (normOneSubgroup F G)).IsMulRightInvariant]

include hi e hc in
/-- A continuous compactly supported kernel gives an integrable partial convolution integrand.
The proof writes the integrand, times a positive-torus bump, as an ambient kernel integrand in
the positive/norm-one coordinates of `G(𝔸)`. -/
theorem integrable_normOnePartialConvolution {κ : A → ℂ} (hκ : Continuous κ)
    (hκc : HasCompactSupport κ) (v : V) (y : A) :
    Integrable (fun n : A¹ => κ ((n : A)⁻¹ * y) * v (q n.val)) dn := by
  let := normalizedPositiveHaarMeasure_sigmaFinite F G T i hi I e hc
  obtain ⟨β, hβ, hβc, hβ0, hβ1⟩ := exists_positiveTorusBump T i hi I e hc
  let κ' : A → ℂ := fun w => κ (w * y)
  have hκ' : Continuous κ' := hκ.comp (continuous_id.mul continuous_const)
  have hκ'c : HasCompactSupport κ' := hκc.comp_homeomorph (Homeomorph.mulRight y)
  have h1 := integrable_kernel_mul (continuous_normOnePositiveKernel T i hi I e hβ hκ' 1)
    (hasCompactSupport_normOnePositiveKernel T i hi I e hβc hκ'c 1)
    (locallyIntegrable_positiveQuotientLpPullback T i hi I e hc v) 1
  rw [integrable_normOneDecomposition_iff F G T i hi I e hc] at h1
  let g : A¹ → ℂ := fun n => κ ((n : A)⁻¹ * y) * v (q n.val)
  have h2 : Integrable (fun p : T⁺ × A¹ => (β p.1 : ℂ) * g p.2) ((ν).prod dn) := by
    refine h1.congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [Function.comp_apply, one_mul, normOnePositiveKernel_positivePointMap_mul,
      mk_positivePointMap_mul, map_one, κ', g, mul_assoc]
  have h3 := h2.integral_norm_prod_right
  have h4 : (fun n : A¹ => ∫ a, ‖(β (a, n).1 : ℂ) * g (a, n).2‖ ∂ν) = fun n => ‖g n‖ := by
    funext n
    simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hβ0 _)]
    rw [integral_mul_const, hβ1, one_mul]
  rw [h4] at h3
  refine (integrable_norm_iff ?_).mp h3
  exact ((hκ.comp (continuous_subtype_val.inv.mul continuous_const)).aestronglyMeasurable).mul
    (stronglyMeasurable_normOnePullback T i hi I e hc v).aestronglyMeasurable

include hi e hc in
/-- For a compact set `K ⊆ G(𝔸)`, the norm of the pulled-back `L²` representative on `K ∩ G(𝔸)¹` is
dominated by an integrable function on `G(𝔸)¹`. -/
theorem exists_integrable_normOnePullback_bound (K : Set A) (hK : IsCompact K) (v : V) :
    ∃ g : A¹ → ℝ, Integrable g dn ∧ (∀ n, 0 ≤ g n) ∧
      ∀ n : A¹, (n : A) ∈ K → ‖v (q n.val)‖ ≤ g n := by
  obtain ⟨χ, hχ1, -, hχc, -⟩ :=
    exists_continuous_one_zero_of_isCompact hK.inv isClosed_empty (disjoint_empty _)
  let κ : A → ℂ := fun w => (χ w : ℂ)
  have hκ : Continuous κ := Complex.continuous_ofReal.comp χ.continuous
  have hκc : HasCompactSupport κ := hχc.comp_left Complex.ofReal_zero
  refine ⟨fun n => ‖κ ((n : A)⁻¹ * 1) * v (q n.val)‖,
    (integrable_normOnePartialConvolution T i hi I e hc hκ hκc v 1).norm,
    fun n => norm_nonneg _, fun n hn => ?_⟩
  have h : χ ((n : A)⁻¹ * 1) = 1 := hχ1 (by rw [mul_one]; exact Set.inv_mem_inv.mpr hn)
  simp only [κ, h, Complex.ofReal_one, one_mul, le_refl]

/-- **The positive-torus kernel identity.** If `β` has normalized integral one, the partial
convolution at `y` is the full right convolution at `y` by the kernel
`normOnePositiveKernel β κ c` with `c` the positive coordinate of `y`. -/
theorem normOnePartialConvolution_eq_smoothing {β : T⁺ → ℝ} (hβ : Continuous β)
    (hβc : HasCompactSupport β) (hβ1 : ∫ a, β a ∂ν = 1) {κ : A → ℂ} (hκ : Continuous κ)
    (hκc : HasCompactSupport κ) (v : V) (y : A) :
    normOnePartialConvolution T i κ v y =
      positiveQuotientLpSmoothing T i (normOnePositiveKernel T i hi I e β κ (π₀ y)) v y := by
  set c := π₀ y with hcdef
  have hint := integrable_kernel_mul (continuous_normOnePositiveKernel T i hi I e hβ hκ c)
    (hasCompactSupport_normOnePositiveKernel T i hi I e hβc hκc c)
    (locallyIntegrable_positiveQuotientLpPullback T i hi I e hc v) y
  unfold positiveQuotientLpSmoothing rightConvolution
  rw [integral_normOneDecomposition_fubini_symm F G T i hi I e hc _ hint]
  have hinner (n : A¹) :
      ∫ a, normOnePositiveKernel T i hi I e β κ c (pp a * n) * (v ∘ q) (y * (pp a * n)) ∂ν =
        κ (pp c * (n : A)⁻¹) * v (q (y * n)) := by
    have hpt (a : T⁺) : normOnePositiveKernel T i hi I e β κ c (pp a * n) *
        (v ∘ q) (y * (pp a * n)) = (β a : ℂ) * (κ (pp c * (n : A)⁻¹) * v (q (y * n))) := by
      rw [normOnePositiveKernel_positivePointMap_mul, Function.comp_apply, ← mul_assoc y,
        ← (positivePointMap_commute F G T i hc a y).eq, mul_assoc (pp a) y,
        mk_positivePointMap_mul, mul_assoc]
    simp_rw [hpt]
    rw [integral_mul_const, integral_complex_ofReal, hβ1, Complex.ofReal_one, one_mul]
  simp_rw [hinner]
  set y₁ : A¹ := π₁ y with hy₁
  have hy : pp c * (y₁ : A) = y := positivePointMap_mul_normOneFactor F G T i hi I e y
  unfold normOnePartialConvolution
  rw [← integral_mul_left_eq_self («μ» := dn) (fun n : A¹ => κ ((n : A)⁻¹ * y) * v (q n.val)) y₁]
  congr 1 with n
  have h1 : ((y₁ * n : A¹) : A)⁻¹ * y = pp c * (n : A)⁻¹ := by
    rw [← hy, Subgroup.coe_mul, mul_inv_rev, mul_assoc, ← mul_assoc (y₁ : A)⁻¹,
      ← (positivePointMap_commute F G T i hc c _).eq, mul_assoc, inv_mul_cancel, mul_one,
      ← (positivePointMap_commute F G T i hc c _).eq]
  have h2 : q ((y₁ * n : A¹) : A) = q (y * n) := by
    rw [← hy, mul_assoc, mk_positivePointMap_mul, Subgroup.coe_mul]
  rw [h1, h2]

include hi e hc in
/-- The partial convolution of a continuous compactly supported kernel is continuous, by
dominated convergence on `G(𝔸)¹`. -/
theorem continuous_normOnePartialConvolution {φ : A → ℂ} (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) (v : V) : Continuous (normOnePartialConvolution T i φ v) := by
  rw [continuous_iff_continuousAt]
  intro y₀
  obtain ⟨U, hU, hUy⟩ := exists_compact_mem_nhds y₀
  obtain ⟨g, hg, hg0, hgK⟩ := exists_integrable_normOnePullback_bound T i hi I e hc
    (U * (tsupport φ)⁻¹) (hU.mul hφc.isCompact.inv) v
  obtain ⟨M, hM⟩ := hφc.exists_bound_of_continuous hφ
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM y₀)
  have hv : AEStronglyMeasurable (fun n : A¹ => v (q n.val)) dn :=
    (stronglyMeasurable_normOnePullback T i hi I e hc v).aestronglyMeasurable
  apply continuousAt_of_dominated (bound := fun n => M * g n)
  · exact Filter.Eventually.of_forall fun y =>
      (hφ.comp (continuous_subtype_val.inv.mul continuous_const)).aestronglyMeasurable.mul hv
  · filter_upwards [hUy] with y hy
    refine Filter.Eventually.of_forall fun n => ?_
    by_cases hn : (n : A)⁻¹ * y ∈ tsupport φ
    · have hnK : (n : A) ∈ U * (tsupport φ)⁻¹ := by
        have h := Set.mul_mem_mul hy (Set.inv_mem_inv.mpr hn)
        rwa [mul_inv_rev, inv_inv, mul_inv_cancel_left] at h
      rw [norm_mul]
      exact mul_le_mul (hM _) (hgK n hnK) (norm_nonneg _) hM0
    · rw [image_eq_zero_of_notMem_tsupport hn, zero_mul, norm_zero]
      exact mul_nonneg hM0 (hg0 n)
  · exact hg.const_mul M
  · exact Filter.Eventually.of_forall fun n =>
      ((hφ.comp (continuous_const.mul continuous_id)).mul continuous_const).continuousAt

omit [(characterRestrict i).range.FiniteIndex]
  [(Measure.haar : Measure (normOneSubgroup F G)).IsMulRightInvariant] in
/-- The partial convolution is left invariant under the rational points, which lie in
`G(𝔸)¹`. -/
theorem normOnePartialConvolution_isLeftInvariant (κ : A → ℂ) (v : V) :
    IsLeftInvariantUnder F G (rationalSubgroup F G) (normOnePartialConvolution T i κ v) := by
  rintro _ ⟨p, rfl⟩ y
  unfold normOnePartialConvolution
  rw [← integral_mul_left_eq_self («μ» := dn)
    (fun n : A¹ => κ ((n : A)⁻¹ * (rational F G p * y)) * v (q n.val)) (rationalNormOne F G p)]
  congr 1 with n
  have hr : rational F G p ∈ Γ := rationalSubgroup_le_positiveRationalSubgroup F G T i ⟨p, rfl⟩
  simp only [Subgroup.coe_mul, rationalNormOne_val, mul_inv_rev, mul_assoc,
    inv_mul_cancel_left]
  rw [LeftCosetSpace.mk_subgroup_mul Γ ⟨_, hr⟩]

omit [(characterRestrict i).range.FiniteIndex]
  [(Measure.haar : Measure (normOneSubgroup F G)).IsMulRightInvariant] in
/-- Right invariance of the kernel passes to the partial convolution. -/
theorem normOnePartialConvolution_mul_right {κ : A → ℂ} {l : A} (hκ : ∀ g, κ (g * l) = κ g)
    (v : V) (y : A) : normOnePartialConvolution T i κ v (y * l) = normOnePartialConvolution T i κ v y := by
  unfold normOnePartialConvolution
  simp only [← mul_assoc, hκ]

include hi e hc in
/-- The reproducing kernel of compact right convolution on the positive rational quotient, with
its mass bound (`quotientConvolutionKernel` for the positive rational subgroup). -/
theorem exists_positiveQuotientSmoothingKernel (h : C_c(A, ℂ)) :
    ∃ w : A → V, Continuous w ∧
      (∀ (x : A) (v : V), Integrable (fun a => h a * v (q (x * a))) dg ∧
        inner ℂ (w x) v = positiveQuotientLpSmoothing T i h v x) ∧
      ∀ (x : A) (M : ℝ), (∀ a, ‖h a‖ ≤ M) →
        ‖w x‖ ^ 2 ≤ M * (∫ a, ‖h a‖ ∂dg) *
          (dΓ).real (Subtype.val ⁻¹' ((fun s => x * s * x⁻¹) '' (tsupport h * (tsupport h)⁻¹))) := by
  let := positiveRationalQuotient_borelSpace F G T i hi I e hc
  let := positiveRationalQuotientHaarMeasure_isLocallyFiniteMeasure F G T i hi I e hc
  let := positiveRationalSubgroupHaarMeasure_isHaarMeasure F G T i hi I e hc
  let := positiveRationalSubgroupHaarMeasure_sigmaFinite F G T i hi I e hc
  let := positiveRationalSubgroupHaarMeasure_isMulRightInvariant F G T i hi I e hc
  exact Langlands.QuotientIntegration.quotientConvolutionKernel Γ
    (isClosed_positiveRationalSubgroup F G T i hi I e hc) dΓ dg dq
    (positiveRationalQuotientHaarMeasure_isCompatible F G T i hi I e hc) h

include hi e hc in
/-- **Uniform growth of partial convolutions.** One exponent `R` serves every continuous
compactly supported kernel: the partial convolution is bounded by a constant times
`H(y)^R ‖v‖`. The proof applies the positive-torus kernel identity, the reproducing-kernel bound
for compact right convolution, and the polynomial growth of the positive rational subgroup mass
of conjugated compact sets; the kernels `normOnePositiveKernel β φ c` all have support in one
compact set. -/
theorem exists_normOnePartialConvolution_growth {N : ℕ} (rho : MatrixRepresentation G (Fin N))
    (hN : 0 < N) (hrho : IsClosedSubgroup rho) :
    ∃ R : ℕ, ∀ φ : A → ℂ, Continuous φ → HasCompactSupport φ → ∃ C : ℝ, 0 ≤ C ∧
      ∀ (v : V) (y : A), ‖normOnePartialConvolution T i φ v y‖ ≤
        C * adelicHeight F G rho y ^ R * ‖v‖ := by
  let := positiveRationalSubgroupHaarMeasure_isHaarMeasure F G T i hi I e hc
  obtain ⟨R, hMass⟩ := adelicPositiveRationalConjugateGrowth_allPoints rho T i hi I e hc hN hrho
  refine ⟨R, fun φ hφ hφc => ?_⟩
  obtain ⟨β, hβ, hβc, -, hβ1⟩ := exists_positiveTorusBump T i hi I e hc
  set S₁ := normOnePositiveKernelSupport T i hi I e β φ
  have hS₁ : IsCompact S₁ := isCompact_normOnePositiveKernelSupport T i hi I e hβc hφc
  obtain ⟨B, hB, hBmass⟩ := hMass (S₁ * S₁⁻¹) (hS₁.mul hS₁.inv)
  obtain ⟨Mβ, hMβ⟩ := hβc.exists_bound_of_continuous hβ
  obtain ⟨Mφ, hMφ⟩ := hφc.exists_bound_of_continuous hφ
  have hMβ0 : 0 ≤ Mβ := (norm_nonneg _).trans (hMβ 1)
  have hMφ0 : 0 ≤ Mφ := (norm_nonneg _).trans (hMφ 1)
  set M := Mβ * Mφ
  have hM0 : 0 ≤ M := mul_nonneg hMβ0 hMφ0
  have hS₁fin : dg S₁ ≠ ⊤ := hS₁.measure_lt_top.ne
  set C₀ := M * (M * (dg).real S₁) * B
  have hC₀ : 0 ≤ C₀ := mul_nonneg (mul_nonneg hM0 (mul_nonneg hM0 measureReal_nonneg)) hB
  refine ⟨Real.sqrt C₀, Real.sqrt_nonneg _, fun v y => ?_⟩
  set c := π₀ y
  let k : C_c(A, ℂ) := ⟨⟨normOnePositiveKernel T i hi I e β φ c,
    continuous_normOnePositiveKernel T i hi I e hβ hφ c⟩,
    hasCompactSupport_normOnePositiveKernel T i hi I e hβc hφc c⟩
  have hkM (w : A) : ‖k w‖ ≤ M := by
    change ‖(β (π₀ w) : ℂ) * φ (pp c * ((π₁ w : A))⁻¹)‖ ≤ M
    rw [norm_mul, Complex.norm_real]
    exact mul_le_mul (hMβ _) (hMφ _) (norm_nonneg _) hMβ0
  have hkint : ∫ w, ‖k w‖ ∂dg ≤ M * (dg).real S₁ := by
    have hsupp : ∀ w ∉ S₁, ‖k w‖ = 0 := fun w hw => by
      rw [norm_eq_zero]
      by_contra hne
      exact hw (support_normOnePositiveKernel_subset T i hi I e β φ c hne)
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hsupp]
    calc ∫ w in S₁, ‖k w‖ ∂dg ≤ ∫ _ in S₁, M ∂dg :=
          setIntegral_mono_on (k.continuous.norm.integrable_of_hasCompactSupport
            k.hasCompactSupport.norm).integrableOn
            (integrableOn_const hS₁fin) hS₁.measurableSet fun w _ => hkM w
      _ = M * (dg).real S₁ := by rw [setIntegral_const, smul_eq_mul, mul_comm]
  obtain ⟨w, -, hPair, hPairBound⟩ := exists_positiveQuotientSmoothingKernel T i hi I e hc k
  have hsub : tsupport k * (tsupport k)⁻¹ ⊆ S₁ * S₁⁻¹ :=
    Set.mul_subset_mul (tsupport_normOnePositiveKernel_subset T i hi I e hβc hφc c)
      (Set.inv_subset_inv.mpr (tsupport_normOnePositiveKernel_subset T i hi I e hβc hφc c))
  have hcpt : IsCompact (Subtype.val ⁻¹' ((fun s => y * s * y⁻¹) '' (S₁ * S₁⁻¹)) : Set Γ) :=
    (isClosed_positiveRationalSubgroup F G T i hi I e hc).isClosedEmbedding_subtypeVal.isCompact_preimage
      ((hS₁.mul hS₁.inv).image ((continuous_const.mul continuous_id).mul continuous_const))
  have hmono : (dΓ).real (Subtype.val ⁻¹' ((fun s => y * s * y⁻¹) '' (tsupport k * (tsupport k)⁻¹))) ≤
      (dΓ).real (Subtype.val ⁻¹' ((fun s => y * s * y⁻¹) '' (S₁ * S₁⁻¹))) :=
    measureReal_mono (Set.preimage_mono (Set.image_mono hsub)) hcpt.measure_lt_top.ne
  have hH : 1 ≤ adelicHeight F G rho y := one_le_adelicHeight F G rho hN y
  have hHpow : 1 ≤ adelicHeight F G rho y ^ R := one_le_pow₀ hH
  have hw : ‖w y‖ ^ 2 ≤ C₀ * (adelicHeight F G rho y ^ R) ^ 2 := by
    calc ‖w y‖ ^ 2 ≤ M * (∫ a, ‖k a‖ ∂dg) * (dΓ).real (Subtype.val ⁻¹'
          ((fun s => y * s * y⁻¹) '' (tsupport k * (tsupport k)⁻¹))) := hPairBound y M hkM
      _ ≤ M * (M * (dg).real S₁) * (B * adelicHeight F G rho y ^ R) := by
          exact mul_le_mul (mul_le_mul_of_nonneg_left hkint hM0) (hmono.trans (hBmass y))
            measureReal_nonneg (mul_nonneg hM0 (mul_nonneg hM0 measureReal_nonneg))
      _ ≤ C₀ * (adelicHeight F G rho y ^ R) ^ 2 := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_left (le_self_pow₀ hHpow (by decide)) hC₀
  have hwy : ‖w y‖ ≤ Real.sqrt C₀ * adelicHeight F G rho y ^ R := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [mul_pow, Real.sq_sqrt hC₀]
    exact hw
  rw [normOnePartialConvolution_eq_smoothing T i hi I e hc hβ hβc hβ1 hφ hφc v y]
  change ‖positiveQuotientLpSmoothing T i k v y‖ ≤ _
  rw [← (hPair y v).2]
  exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hwy (norm_nonneg _))

section Cuspidality

variable (hPD : ParabolicDynamicStatement.{u}) (hG : IsConnectedReductive G)

local notation "S" => fullAEL2CuspidalSubmodule F G hPD hG T i hi I e hc

private theorem positiveQuotientLpSmoothing_hasZeroProperParabolicConstantTerms
    (k : C_c(A, ℂ)) {v : V} (hv : v ∈ S) :
    HasZeroProperParabolicConstantTerms (positiveQuotientLpSmoothing T i k v) := by
  obtain ⟨w, hw, hPair, _⟩ := exists_positiveQuotientSmoothingKernel T i hi I e hc k
  let f := positiveQuotientLpSmoothing T i k v
  have hf : Continuous f := by
    have heq : f = fun x => inner ℂ (w x) v := funext fun x => (hPair x v).2.symm
    rw [heq]
    exact hw.inner continuous_const
  let hInv := positiveQuotientLpSmoothing_invariant T i k v
  let φ : C(Q, ℂ) := ⟨LeftCosetSpace.lift Γ f hInv, LeftCosetSpace.continuous_lift Γ _ _ hf⟩
  have hkI : Integrable (k : A → ℂ) dg := k.continuous.integrable_of_hasCompactSupport k.hasCompactSupport
  have hφCus := (groupSchemeFullAEL2ContinuousCuspidality F G hPD hG T i hi I e hc φ _
      (positiveQuotientLpSmoothing_ae_eq T i hi I e hc k hkI v)).mp
    (haarQuotientL2IntegratedAction_mem_fullAEL2CuspidalSubmodule F G hPD hG T i hi I e hc dg k hkI v hv)
  exact hasZeroProperParabolicConstantTerms_of_normalized hPD hG _ hφCus

/-- The proper parabolic constant terms of the partial convolution of a cuspidal class
vanish pointwise. The positive coordinate is constant along each radical orbit. -/
theorem normOnePartialConvolution_hasZeroProperParabolicConstantTerms
    {κ : A → ℂ} (hκ : Continuous κ) (hκc : HasCompactSupport κ) {v : V} (hv : v ∈ S) :
    HasZeroProperParabolicConstantTerms (normOnePartialConvolution T i κ v) := by
  obtain ⟨β, hβ, hβc, -, hβ1⟩ := exists_positiveTorusBump T i hi I e hc
  intro P U p r _ _ hp hr hpProper
  let := hG.isAffineHom
  let : IsClosedImmersion p.hom.hom.left := hp.isClosedSubgroup
  let : IsAffineHom P.X.hom := by rw [← Over.w p.hom.hom]; infer_instance
  let P' : ProperRationalParabolic G := ⟨⟨SubgroupFunctor.range p, ⟨P, p, hp, rfl⟩⟩, hpProper⟩
  have hEq : properRationalParabolicRadicals hPD hG P' = SubgroupFunctor.range (r ≫ p) :=
    properRationalParabolicRadicals_eq hPD hG hp hpProper hr.isGeometricUnipotentRadical.isUnipotentRadical
  have hU (n : AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (r ≫ p))) :
      n.val ∈ A¹ := by
    obtain ⟨u, hu⟩ := n
    rw [← hEq] at hu
    exact (properParabolicNormOneInclusion F G hPD hG P' ⟨u, hu⟩).property
  funext y
  let k : C_c(A, ℂ) := ⟨⟨normOnePositiveKernel T i hi I e β κ (π₀ y),
    continuous_normOnePositiveKernel T i hi I e hβ hκ _⟩,
    hasCompactSupport_normOnePositiveKernel T i hi I e hβc hκc _⟩
  have hCus := positiveQuotientLpSmoothing_hasZeroProperParabolicConstantTerms T i hi I e hc hPD hG k hv
  calc
    _ = subgroupConstantTerm F (r ≫ p) (positiveQuotientLpSmoothing T i k v) y := by
      unfold subgroupConstantTerm
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      let n : AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (r ≫ p)) := Quotient.out x
      have hπ : π₀ (n.val * y) = π₀ y := by
        rw [map_mul, positiveFactor_normOne F G T i hi I e ⟨n.val, hU n⟩, one_mul]
      change normOnePartialConvolution T i κ v (n.val * y) =
        positiveQuotientLpSmoothing T i k v (n.val * y)
      rw [normOnePartialConvolution_eq_smoothing T i hi I e hc hβ hβc hβ1 hκ hκc, hπ]
      rfl
    _ = 0 := congrFun (hCus P U p r hp hr hpProper) y

end Cuspidality

include hi e hc in
/-- Partial convolution intertwines right convolution on the kernel and on the output.
On the product of the two integration spaces, compact kernel supports confine the
norm-one variable to a compact set where the pulled-back representative has an
integrable majorant. -/
theorem normOnePartialConvolution_rightConvolution {k φ : A → ℂ} (hk : Continuous k)
    (hkc : HasCompactSupport k) (hφ : Continuous φ) (hφc : HasCompactSupport φ) (v : V) :
    normOnePartialConvolution T i (rightConvolution F G k φ) v =
      rightConvolution F G k (normOnePartialConvolution T i φ v) := by
  funext y
  let D : Set A := ({y} : Set A) * tsupport k * (tsupport φ)⁻¹
  have hD : IsCompact D := (isCompact_singleton.mul hkc.isCompact).mul hφc.isCompact.inv
  obtain ⟨g, hg, hg0, hgD⟩ := exists_integrable_normOnePullback_bound T i hi I e hc D hD v
  obtain ⟨M, hM⟩ := hφc.exists_bound_of_continuous hφ
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 1)
  let f (n : A¹) (a : A) := k a * φ ((n : A)⁻¹ * y * a) * v (q n.val)
  have hf : Integrable (Function.uncurry f) ((dn).prod dg) := by
    have hcont : Continuous (fun p : A¹ × A => k p.2 * φ ((p.1 : A)⁻¹ * y * p.2)) :=
      (hk.comp continuous_snd).mul
        (hφ.comp (((continuous_subtype_val.comp continuous_fst).inv.mul continuous_const).mul continuous_snd))
    have hmeas : AEStronglyMeasurable (Function.uncurry f) ((dn).prod dg) :=
      hcont.aestronglyMeasurable.mul
        ((stronglyMeasurable_normOnePullback T i hi I e hc v).comp_measurable
          measurable_fst).aestronglyMeasurable
    have hkI : Integrable (fun a => ‖k a‖) dg :=
      hk.norm.integrable_of_hasCompactSupport hkc.norm
    have hint := hg.mul_prod (hkI.const_mul M)
    refine hint.mono' hmeas (Filter.Eventually.of_forall fun p => ?_)
    obtain ⟨n, a⟩ := p
    change ‖f n a‖ ≤ g n * (M * ‖k a‖)
    by_cases ha : a ∈ tsupport k
    · by_cases hna : (n : A)⁻¹ * y * a ∈ tsupport φ
      · have hn : (n : A) ∈ D := by
          have hn' := Set.mul_mem_mul (Set.mul_mem_mul (Set.mem_singleton y) ha)
            (Set.inv_mem_inv.mpr hna)
          rwa [mul_assoc (n : A)⁻¹, mul_inv_rev, inv_inv, mul_inv_cancel_left] at hn'
        simp only [f, norm_mul]
        calc
          ‖k a‖ * ‖φ ((n : A)⁻¹ * y * a)‖ * ‖v (q n.val)‖
            ≤ ‖k a‖ * M * g n :=
              mul_le_mul (mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _)) (hgD n hn)
                (norm_nonneg _) (mul_nonneg (norm_nonneg _) hM0)
          _ = g n * (M * ‖k a‖) := by ring
      · simp [f, image_eq_zero_of_notMem_tsupport hna, mul_nonneg (hg0 n) (mul_nonneg hM0 (norm_nonneg _))]
    · simp [f, image_eq_zero_of_notMem_tsupport ha]
  calc
    _ = ∫ n, (∫ a, f n a ∂dg) ∂dn := by
      simp only [normOnePartialConvolution, rightConvolution, f, integral_mul_const]
    _ = ∫ a, (∫ n, f n a ∂dn) ∂dg := integral_integral_swap hf
    _ = _ := by
      simp only [normOnePartialConvolution, rightConvolution, f, mul_assoc, integral_const_mul]

include hi e hc in
/-- Partial convolution is additive in finite sums of continuous compactly supported kernels. -/
theorem normOnePartialConvolution_sum {J : Type*} (s : Finset J) (κ : J → A → ℂ)
    (hκ : ∀ j ∈ s, Continuous (κ j)) (hκc : ∀ j ∈ s, HasCompactSupport (κ j)) (v : V) (y : A) :
    normOnePartialConvolution T i (fun a => ∑ j ∈ s, κ j a) v y =
      ∑ j ∈ s, normOnePartialConvolution T i (κ j) v y := by
  unfold normOnePartialConvolution
  simp only [Finset.sum_mul]
  exact integral_finsetSum s fun j hj =>
    integrable_normOnePartialConvolution T i hi I e hc (hκ j hj) (hκc j hj) v y

end Langlands.Automorphic.GroupSchemeFunctions
