import Langlands.GroupScheme.Examples.SU3RootUnitaryIntegralChart
import Langlands.GroupScheme.Examples.SU3RootUnitaryLattices
import Langlands.GroupScheme.Examples.SU3RootFiltration
import Langlands.GroupScheme.IntegralModelReduction

/-! # The integral models `X_{r,s}` of the ramified quadratic unitary group

Let `ω` be a ramified quadratic valuation of `L / K` (`IsRamifiedQuadraticValuation`) and let
`O ⊆ K` be its ring of integers (`IsValuationIntegers`). For real depths `r, s` the lattice chart
`(Y_r, Z_{min(s, 2r)}, λ)` with `λ ∈ L^{tr=1,max}` has integral cocycle coefficients, and its
integral model is the smooth affine group scheme `X_{r,s}` of Kaletha–Prasad Appendix C.4. Its
integral points are exactly `X(K)_r · Z(K)_s` (Lemma C.4.2, Corollary C.4.3), and coordinatewise
ordered depths give transition homomorphisms acting diagonally on the coordinates.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry

attribute [local instance] CategoryTheory.Hom.group

namespace Langlands.GroupScheme.SU3Root

/-! ### Normality of the central filtration -/

namespace Parameters

variable {L : Type v} [Field L] {c : RingInvolution L}
  (omega : AddValuation L (WithTop ℝ)) (hinv : ∀ z : L, omega (c.bar z) = omega z)

/-- Elements with vanishing first coordinate are central. -/
theorem conj_eq_of_first_eq_zero (g n : Parameters c) (hn : n.first = 0) :
    g * n * g⁻¹ = n := by
  apply Parameters.ext
  · simp [hn]
  · simp only [second_mul, first_mul, first_inv, second_inv, hn, map_zero, map_neg, mul_zero,
      add_zero, mul_neg]
    linear_combination g.equation

instance centralFiltration_normal (r : ℝ) : (centralFiltration omega hinv r).Normal where
  conj_mem n hn g := by
    rw [conj_eq_of_first_eq_zero g n hn.1]
    exact hn

/-- Membership in `filtration ⊔ centralFiltration` is a product decomposition. -/
theorem mem_filtration_sup_centralFiltration (r s : ℝ) (p : Parameters c) :
    p ∈ filtration omega hinv r ⊔ centralFiltration omega hinv s ↔
      ∃ x ∈ filtration omega hinv r, ∃ z ∈ centralFiltration omega hinv s, x * z = p :=
  Subgroup.mem_sup_of_normal_right

/-- Central elements of depth at least `2r` already lie in the filtration subgroup of depth
`r`, so a central depth above `2r` may be lowered to `2r`. -/
theorem filtration_sup_centralFiltration_min (r s : ℝ) :
    filtration omega hinv r ⊔ centralFiltration omega hinv (min s (2 * r)) =
      filtration omega hinv r ⊔ centralFiltration omega hinv s := by
  rcases le_total s (2 * r) with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h]
    have hle : ∀ t, 2 * r ≤ t →
        centralFiltration omega hinv t ≤ filtration omega hinv r := by
      intro t ht p hp
      exact le_trans (WithTop.coe_le_coe.mpr ht) hp.2
    rw [sup_eq_left.mpr (hle _ le_rfl), sup_eq_left.mpr (hle _ h)]

end Parameters

/-! ### Rings of integers -/

section Integers

variable (O K : Type*) {L : Type*} [CommRing O] [Field K] [Algebra O K] [Field L] [Algebra K L]

/-- `O` is the ring of integers of `K` for `ω`: an element of `K` comes from `O` exactly when its
value is nonnegative. -/
def IsValuationIntegers (ω : AddValuation L (WithTop ℝ)) : Prop :=
  ∀ a : K, a ∈ (algebraMap O K).range ↔ 0 ≤ ω (algebraMap K L a)

variable {O K} {ω : AddValuation L (WithTop ℝ)}

theorem IsValuationIntegers.exists_eq (hO : IsValuationIntegers O K ω) {a : K}
    (ha : 0 ≤ ω (algebraMap K L a)) : ∃ b : O, algebraMap O K b = a :=
  (hO a).mpr ha

theorem IsValuationIntegers.nonneg (hO : IsValuationIntegers O K ω) (b : O) :
    0 ≤ ω (algebraMap K L (algebraMap O K b)) :=
  (hO _).mp ⟨b, rfl⟩

end Integers

/-! ### The lattice charts and the models `X_{r,s}` -/

section LatticeModel

variable {O K L : Type u} [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K]
  [Field L] [Algebra K L] [Algebra.IsQuadraticExtension K L] [Algebra.IsSeparable K L]
  {ω : AddValuation L (WithTop ℝ)}

local notation "σ" => conjugation K L

namespace IsRamifiedQuadraticValuation

variable (hω : IsRamifiedQuadraticValuation K L ω)

/-- **Kaletha–Prasad's subgroup `X(K)_r · Z(K)_s`** of the rational points of the unitary
parameter group: `X(K)_r = {(u, v) | ω(v) ≥ 2r + μ}` is the filtration subgroup of depth
`r + μ/2` and `Z(K)_s = {(0, v) | ω(v) ≥ s + μ}` is the central filtration subgroup of depth
`s + μ`. Since `Z(K)_s` is central, the join is the product set. -/
def filtrationProduct (r s : ℝ) : Subgroup (rationalParameters K L) :=
  Parameters.filtration ω hω.bar_eq (r + mu K L ω / 2) ⊔
    Parameters.centralFiltration ω hω.bar_eq (s + mu K L ω)

theorem mem_filtrationProduct_iff (r s : ℝ) (p : rationalParameters K L) :
    p ∈ hω.filtrationProduct r s ↔
      ∃ x : rationalParameters K L, ((2 * r + mu K L ω : ℝ) : WithTop ℝ) ≤ ω x.second ∧
        ∃ z : rationalParameters K L, z.first = 0 ∧
          ((s + mu K L ω : ℝ) : WithTop ℝ) ≤ ω z.second ∧ x * z = p := by
  rw [filtrationProduct, Parameters.mem_filtration_sup_centralFiltration]
  have h2 : 2 * (r + mu K L ω / 2) = 2 * r + mu K L ω := by ring
  simp only [Parameters.mem_filtration, Parameters.mem_centralFiltration, h2, and_assoc]

/-- The central depth can be lowered to `min s (2r)` without changing `X(K)_r · Z(K)_s`. -/
theorem filtrationProduct_min (r s : ℝ) :
    hω.filtrationProduct r (min s (2 * r)) = hω.filtrationProduct r s := by
  have h : ∀ t : ℝ, min t (2 * r) + mu K L ω = min (t + mu K L ω) (2 * (r + mu K L ω / 2)) := by
    intro t
    rw [show 2 * (r + mu K L ω / 2) = 2 * r + mu K L ω by ring, min_add_add_right]
  rw [filtrationProduct, filtrationProduct, h,
    Parameters.filtration_sup_centralFiltration_min]

/-- For `s ≤ 2r` the cocycle coefficients of `latticeData r s` are integral (this needs no
integrality of `2r`). -/
theorem omega_latticeData_coeff_nonneg_of_le (r s : ℝ) (hs : s ≤ 2 * r)
    (i j : ULift.{u} (Fin 2)) :
    0 ≤ ω (algebraMap K L ((hω.latticeData r s).coeff i j)) := by
  have h := (hω.latticeData r s).coeff_mul_center i j
  rw [latticeData_center, latticeData_traceOne, latticeData_basis, latticeData_basis] at h
  rw [← hω.le_omega_mul_latticeCenter_iff s, h]
  refine le_trans ?_ (hω.le_omega_correction r (hω.le_omega_latticeBasis r _)
    (hω.le_omega_latticeBasis r _))
  rw [WithTop.coe_le_coe]
  linarith

variable (hO : IsValuationIntegers O K ω)

/-- The lattice chart of `X_{r,s}`: the basis `(ϖ^⌈r⌉, ϖ^⌈r-1/2⌉ π)` of `Y_r`, the trace-one
element `λ ∈ L^{tr=1,max}` and the generator of `Z_{min(s, 2r)}`, with its integral cocycle
coefficients. -/
def latticeChart (r s : ℝ) : IntegralChart O K L (ULift.{u} (Fin 2)) where
  data := hω.latticeData r (min s (2 * r))
  coeff i j := (hO.exists_eq
    (hω.omega_latticeData_coeff_nonneg_of_le r (min s (2 * r)) (min_le_right _ _) i j)).choose
  algebraMap_coeff i j := (hO.exists_eq
    (hω.omega_latticeData_coeff_nonneg_of_le r (min s (2 * r)) (min_le_right _ _) i j)).choose_spec

omit [IsDomain O] [IsFractionRing O K] in
@[simp] theorem latticeChart_data (r s : ℝ) :
    (hω.latticeChart hO r s).data = hω.latticeData r (min s (2 * r)) := rfl

/-- **The integral model `X_{r,s}`** of the unitary parameter group `U_{L/K}`, for arbitrary
real depths `r, s`. -/
def latticeModel (r s : ℝ) : IntegralModel O K (unitaryParameterGroup K L) :=
  (hω.latticeChart hO r s).model

theorem latticeModel_eq (r s : ℝ) : hω.latticeModel hO r s = (hω.latticeChart hO r s).model :=
  rfl

/-- `X_{r,s}` is smooth. -/
theorem latticeModel_isSmooth (r s : ℝ) : (hω.latticeModel hO r s).IsSmooth :=
  (hω.latticeChart hO r s).model_isSmooth

/-- `X_{r,s}` has geometrically connected fibres. -/
theorem latticeModel_hasGeometricallyConnectedFibres (r s : ℝ) :
    (hω.latticeModel hO r s).HasGeometricallyConnectedFibres :=
  (hω.latticeChart hO r s).model_geometricallyConnected

/-- `X_{r,s}` is affine over `Spec O`. -/
instance latticeModel_isAffineHom (r s : ℝ) : IsAffineHom (hω.latticeModel hO r s).group.X.hom :=
  (hω.latticeModel hO r s).affine

/-! #### The integral-point image -/

omit [IsDomain O] [IsFractionRing O K] in
include hO in
/-- An element with integral coordinates in `latticeBasis r` has value at least `r`. -/
theorem le_omega_sum_latticeBasis (r : ℝ) (a : ULift.{u} (Fin 2) → O) :
    (r : WithTop ℝ) ≤ ω (∑ i, algebraMap K L (algebraMap O K (a i)) * hω.latticeBasis r i.down) := by
  apply ω.map_le_sum
  intro i _
  rw [ω.map_mul]
  calc (r : WithTop ℝ) = 0 + (r : WithTop ℝ) := (zero_add _).symm
    _ ≤ _ := add_le_add (hO.nonneg (a i)) (hω.le_omega_latticeBasis r i.down)

omit [IsDomain O] [IsFractionRing O K] in
include hO in
/-- **Kaletha–Prasad Lemma C.4.2.** For `s ≤ 2r`, the field points of the chart
`latticeData r s` with coordinates in `O` form exactly `X(K)_r · Z(K)_s`. -/
theorem exists_fieldPoint_iff (r s : ℝ) (hs : s ≤ 2 * r) (p : rationalParameters K L) :
    (∃ (a : ULift.{u} (Fin 2) → O) (b : O), p =
        fieldPoint (hω.latticeData r s) (fun i => algebraMap O K (a i)) (algebraMap O K b)) ↔
      p ∈ hω.filtrationProduct r s := by
  rw [mem_filtrationProduct_iff]
  constructor
  · rintro ⟨a, b, rfl⟩
    set D : CoordinateData K L (ULift.{u} (Fin 2)) := hω.latticeData r s
    set u := (fieldPoint D (fun i => algebraMap O K (a i)) (algebraMap O K b)).first with hu_def
    have hu : (r : WithTop ℝ) ≤ ω u := by
      rw [hu_def, first_fieldPoint]
      simp only [D, latticeData_basis]
      exact hω.le_omega_sum_latticeBasis hO r a
    have hx : hω.traceOneMax * (u * σ u) + σ (hω.traceOneMax * (u * σ u)) = u * σ u := by
      rw [map_mul, map_mul, conjugation_involutive K L u]
      linear_combination (u * σ u) * hω.traceOneMax_add
    have hz : algebraMap K L (algebraMap O K b) * hω.latticeCenter s +
        σ (algebraMap K L (algebraMap O K b) * hω.latticeCenter s) = 0 := by
      rw [map_mul, AlgEquiv.commutes]
      linear_combination algebraMap K L (algebraMap O K b) * hω.latticeCenter_add s
    refine ⟨⟨(u, hω.traceOneMax * (u * σ u)), hx⟩, ?_,
      ⟨(0, algebraMap K L (algebraMap O K b) * hω.latticeCenter s), by simpa using hz⟩, rfl, ?_, ?_⟩
    · change _ ≤ ω (hω.traceOneMax * (u * σ u))
      exact hω.le_omega_traceOneMax_mul r hu
    · change _ ≤ ω (algebraMap K L (algebraMap O K b) * hω.latticeCenter s)
      exact (hω.le_omega_mul_latticeCenter_iff s _).mpr (hO.nonneg b)
    · apply Parameters.ext
      · change u + 0 = u
        rw [add_zero]
      · change hω.traceOneMax * (u * σ u) +
          algebraMap K L (algebraMap O K b) * hω.latticeCenter s + u * σ 0 = _
        rw [second_fieldPoint, ← hu_def]
        simp only [D, latticeData_center, latticeData_traceOne, map_zero, mul_zero, add_zero]
        ring
  · rintro ⟨x, hx, z, hz0, hz, rfl⟩
    set D : CoordinateData K L (ULift.{u} (Fin 2)) := hω.latticeData r s
    set u := x.first with hu_def
    -- Lemma 3.2.2: the first coordinate lies in `Y_r`.
    have hu : (r : WithTop ℝ) ≤ ω u := hω.le_omega_of_le_omega_second x.equation r hx
    have hrepr : ∀ i, 0 ≤ ω (algebraMap K L (D.basis.repr u i)) := by
      intro i
      change 0 ≤ ω (algebraMap K L
        (((hω.latticeBasis r).reindex Equiv.ulift.symm).repr u i))
      rw [Module.Basis.repr_reindex_apply]
      exact (hω.le_omega_iff_latticeBasis r u).mp hu _
    -- The remaining coordinate lies in `Z_s`.
    set w := (x.second - hω.traceOneMax * (u * σ u)) + z.second with hw_def
    have hzeq : z.second + σ z.second = 0 := by
      have := z.equation
      rw [hz0, map_zero, mul_zero] at this
      exact this
    have hw : w + σ w = 0 := by
      have hxeq := x.equation
      simp only [fieldInvolution_bar] at hxeq hzeq
      rw [hw_def, map_add, map_sub, map_mul, map_mul, conjugation_involutive K L u]
      linear_combination hxeq + hzeq - (u * σ u) * hω.traceOneMax_add
    have hwval : ((s + mu K L ω : ℝ) : WithTop ℝ) ≤ ω w := by
      have h1 : ((s + mu K L ω : ℝ) : WithTop ℝ) ≤ ((2 * r + mu K L ω : ℝ) : WithTop ℝ) :=
        WithTop.coe_le_coe.mpr (by linarith)
      refine ω.map_le_add (le_trans h1 ?_) hz
      rw [sub_eq_add_neg]
      refine ω.map_le_add hx ?_
      rw [ω.map_neg]
      exact hω.le_omega_traceOneMax_mul r hu
    obtain ⟨c, hc⟩ := hω.exists_mul_latticeCenter s hw
    have hcval : 0 ≤ ω (algebraMap K L c) := by
      rw [← hω.le_omega_mul_latticeCenter_iff s, hc]
      exact hwval
    obtain ⟨b, hb⟩ := hO.exists_eq hcval
    choose a ha using fun i => hO.exists_eq (hrepr i)
    refine ⟨a, b, ?_⟩
    have hfirst : (fieldPoint D (fun i => algebraMap O K (a i)) (algebraMap O K b)).first = u := by
      rw [first_fieldPoint]
      simp only [ha]
      conv_rhs => rw [← D.basis.sum_repr u]
      simp only [Algebra.smul_def]
    apply Parameters.ext
    · rw [hfirst]
      change x.first + z.first = u
      rw [hz0, add_zero]
    · rw [second_fieldPoint, hfirst, hb]
      change x.second + z.second + x.first * σ z.first = _
      have hDc : D.center = hω.latticeCenter s := hω.latticeData_center r s
      have hDt : D.traceOne = hω.traceOneMax := hω.latticeData_traceOne r s
      rw [hDc, hDt, hc, hz0, map_zero, mul_zero, add_zero, hw_def]
      ring

/-- **Integral points of `X_{r,s}` (Kaletha–Prasad Lemma C.4.2 and Corollary C.4.3).** A
rational point of the unitary parameter group is an integral point of `X_{r,s}` exactly when
it lies in `X(K)_r · Z(K)_s`. -/
theorem mem_integralPoints_latticeModel_iff (r s : ℝ)
    (g : rationalPoints (unitaryParameterGroup K L)) :
    g ∈ (hω.latticeModel hO r s).integralPoints ↔
      unitaryRationalPointsEquiv K L g ∈ hω.filtrationProduct r s := by
  rw [latticeModel_eq, IntegralChart.mem_integralPoints_iff, latticeChart_data,
    ← hω.filtrationProduct_min r s,
    ← hω.exists_fieldPoint_iff hO r (min s (2 * r)) (min_le_right _ _)]

/-- **The integral-point image.** Under the identification of `U_{L/K}(K)` with the field
parameters, the integral points of `X_{r,s}` are exactly `X(K)_r · Z(K)_s`. -/
theorem integralPoints_latticeModel_map (r s : ℝ) :
    (hω.latticeModel hO r s).integralPoints.map
        (unitaryRationalPointsEquiv K L).toMonoidHom = hω.filtrationProduct r s := by
  ext p
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact (hω.mem_integralPoints_latticeModel_iff hO r s g).mp hg
  · intro hp
    refine ⟨(unitaryRationalPointsEquiv K L).symm p, ?_, MulEquiv.apply_symm_apply _ _⟩
    rw [hω.mem_integralPoints_latticeModel_iff hO r s, MulEquiv.apply_symm_apply]
    exact hp

/-! #### Transition homomorphisms -/

/-- A lift of the base uniformizer `ϖ` to `O`. -/
def integralUniformizer : O :=
  (hO.exists_eq (a := hω.baseUniformizer) (by
    rw [hω.omega_baseUniformizer]
    exact WithTop.coe_nonneg.mpr zero_le_one)).choose

omit [IsDomain O] [IsFractionRing O K] in
@[simp] theorem algebraMap_integralUniformizer :
    algebraMap O K (hω.integralUniformizer hO) = hω.baseUniformizer :=
  (hO.exists_eq (a := hω.baseUniformizer) (by
    rw [hω.omega_baseUniformizer]
    exact WithTop.coe_nonneg.mpr zero_le_one)).choose_spec

/-- The exponent of `ϖ` in the transition on the vector coordinate `i` (from depth `r₂` to
depth `r₁`): `⌈r₂⌉ - ⌈r₁⌉` for `i = 0` and `⌈r₂ - 1/2⌉ - ⌈r₁ - 1/2⌉` for `i = 1`. -/
def vecExponent (r₁ r₂ : ℝ) (i : Fin 2) : ℤ :=
  ![⌈r₂⌉ - ⌈r₁⌉, ⌈r₂ - 1 / 2⌉ - ⌈r₁ - 1 / 2⌉] i

/-- The exponent of `ϖ` in the transition on the scalar coordinate (from central depth `s₂` to
`s₁`, after lowering both to `min s (2r)`). -/
def scalarExponent (r₁ s₁ r₂ s₂ : ℝ) : ℤ :=
  ⌈min s₂ (2 * r₂) + mu K L ω - hω.traceZeroValue⌉ -
    ⌈min s₁ (2 * r₁) + mu K L ω - hω.traceZeroValue⌉

omit hω in
@[simp] theorem vecExponent_zero (r₁ r₂ : ℝ) : vecExponent r₁ r₂ 0 = ⌈r₂⌉ - ⌈r₁⌉ := rfl

omit hω in
@[simp] theorem vecExponent_one (r₁ r₂ : ℝ) :
    vecExponent r₁ r₂ 1 = ⌈r₂ - 1 / 2⌉ - ⌈r₁ - 1 / 2⌉ := rfl

omit hω in
theorem vecExponent_nonneg {r₁ r₂ : ℝ} (hr : r₁ ≤ r₂) (i : Fin 2) : 0 ≤ vecExponent r₁ r₂ i := by
  revert i
  rw [Fin.forall_fin_two, vecExponent_zero, vecExponent_one, sub_nonneg, sub_nonneg]
  exact ⟨Int.ceil_mono hr, Int.ceil_mono (by linarith)⟩

theorem scalarExponent_nonneg {r₁ s₁ r₂ s₂ : ℝ} (hr : r₁ ≤ r₂) (hs : s₁ ≤ s₂) :
    0 ≤ hω.scalarExponent r₁ s₁ r₂ s₂ := by
  rw [scalarExponent, sub_nonneg]
  apply Int.ceil_mono
  have : min s₁ (2 * r₁) ≤ min s₂ (2 * r₂) := min_le_min hs (by linarith)
  linarith

/-- The diagonal matrix of the transition. -/
def transitionMatrix (r₁ r₂ : ℝ) (i l : ULift.{u} (Fin 2)) : O :=
  if i = l then hω.integralUniformizer hO ^ (vecExponent r₁ r₂ i.down).toNat else 0

/-- The scalar of the transition. -/
def transitionScalar (r₁ s₁ r₂ s₂ : ℝ) : O :=
  hω.integralUniformizer hO ^ (hω.scalarExponent r₁ s₁ r₂ s₂).toNat

omit [IsDomain O] [IsFractionRing O K] in
theorem algebraMap_pow_toNat (n : ℤ) (hn : 0 ≤ n) :
    algebraMap O K (hω.integralUniformizer hO ^ n.toNat) = hω.baseUniformizer ^ n := by
  rw [map_pow, algebraMap_integralUniformizer, ← zpow_natCast, Int.toNat_of_nonneg hn]

theorem latticeBasis_eq_mul (r₁ r₂ : ℝ) (i : Fin 2) :
    hω.latticeBasis r₂ i = algebraMap K L (hω.baseUniformizer ^ vecExponent r₁ r₂ i) *
      hω.latticeBasis r₁ i := by
  have hϖ := hω.baseUniformizer_ne_zero
  revert i
  rw [Fin.forall_fin_two]
  constructor
  · rw [latticeBasis_zero, latticeBasis_zero, vecExponent_zero, ← map_mul, ← zpow_add₀ hϖ,
      sub_add_cancel]
  · rw [latticeBasis_one, latticeBasis_one, vecExponent_one, ← mul_assoc, ← map_mul,
      ← zpow_add₀ hϖ, sub_add_cancel]

theorem latticeCenter_eq_mul (s₁ s₂ : ℝ) :
    hω.latticeCenter s₂ = algebraMap K L (hω.baseUniformizer ^
      (⌈s₂ + mu K L ω - hω.traceZeroValue⌉ - ⌈s₁ + mu K L ω - hω.traceZeroValue⌉)) *
        hω.latticeCenter s₁ := by
  rw [latticeCenter, latticeCenter, ← mul_assoc, ← map_mul,
    ← zpow_add₀ hω.baseUniformizer_ne_zero, sub_add_cancel]

omit [IsDomain O] [IsFractionRing O K] in
/-- The transition is an integral change of lattice chart. -/
theorem isChartChange_transition {r₁ s₁ r₂ s₂ : ℝ} (hr : r₁ ≤ r₂) (hs : s₁ ≤ s₂) :
    (hω.latticeChart hO r₂ s₂).data.IsChartChange (hω.latticeChart hO r₁ s₁).data
      (fun i l => algebraMap O K (hω.transitionMatrix hO r₁ r₂ i l))
      (algebraMap O K (hω.transitionScalar hO r₁ s₁ r₂ s₂)) where
  traceOne_eq := by
    rw [latticeChart_data, latticeChart_data, latticeData_traceOne, latticeData_traceOne]
  basis_eq i := by
    rw [latticeChart_data, latticeData_basis, Finset.sum_eq_single i]
    · rw [latticeChart_data, latticeData_basis, transitionMatrix, ite_eq_left rfl,
        hω.algebraMap_pow_toNat hO _ (vecExponent_nonneg hr _)]
      exact hω.latticeBasis_eq_mul r₁ r₂ i.down
    · intro l _ hl
      rw [transitionMatrix, ite_eq_right (Ne.symm hl), map_zero, map_zero, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ i) h
  center_eq := by
    rw [latticeChart_data, latticeChart_data, latticeData_center, latticeData_center,
      transitionScalar, hω.algebraMap_pow_toNat hO _ (hω.scalarExponent_nonneg hr hs),
      scalarExponent]
    exact hω.latticeCenter_eq_mul _ _

/-- **Transition homomorphisms.** For `r₁ ≤ r₂` and `s₁ ≤ s₂`, the homomorphism
`X_{r₂,s₂} → X_{r₁,s₁}` of integral models extending the identity of `U_{L/K}`. -/
def latticeTransition {r₁ s₁ r₂ s₂ : ℝ} (hr : r₁ ≤ r₂) (hs : s₁ ≤ s₂) :
    (hω.latticeModel hO r₂ s₂).Hom (hω.latticeModel hO r₁ s₁) (𝟙 _) :=
  (hω.latticeChart hO r₂ s₂).chartHom (hω.latticeChart hO r₁ s₁)
    (hω.transitionMatrix hO r₁ r₂) (hω.transitionScalar hO r₁ s₁ r₂ s₂)
    (hω.isChartChange_transition hO hr hs)

/-- The underlying group-scheme homomorphism of a transition is the linear homomorphism of
bilinear coordinate groups with the diagonal matrix and scalar of the transition. -/
theorem latticeTransition_hom {r₁ s₁ r₂ s₂ : ℝ} (hr : r₁ ≤ r₂) (hs : s₁ ≤ s₂) :
    (hω.latticeTransition hO hr hs).hom =
      BilinearCoordinate.linearHom (CommRingCat.of O) (hω.transitionMatrix hO r₁ r₂)
        (hω.transitionScalar hO r₁ s₁ r₂ s₂)
        ((hω.latticeChart hO r₂ s₂).isCompatible_of_isChartChange (hω.latticeChart hO r₁ s₁)
          _ _ (hω.isChartChange_transition hO hr hs)) :=
  rfl

/-- On integral vector coordinates, the transition multiplies the coordinate `i` by
`ϖ^{vecExponent r₁ r₂ i}`. -/
theorem vec_integralCoordinatesEquiv_latticeTransition {r₁ s₁ r₂ s₂ : ℝ} (hr : r₁ ≤ r₂)
    (hs : s₁ ≤ s₂) (x : (hω.latticeModel hO r₂ s₂).integralSections) (i : ULift.{u} (Fin 2)) :
    ((hω.latticeChart hO r₁ s₁).integralCoordinatesEquiv
        (rationalPoints.map (hω.latticeTransition hO hr hs).hom x)).vec i =
      ((hω.latticeChart hO r₂ s₂).integralCoordinatesEquiv x).vec i *
        hω.integralUniformizer hO ^ (vecExponent r₁ r₂ i.down).toNat := by
  have key := (hω.latticeChart hO r₂ s₂).integralCoordinatesEquiv_chartHom
    (hω.latticeChart hO r₁ s₁) (hω.transitionMatrix hO r₁ r₂)
    (hω.transitionScalar hO r₁ s₁ r₂ s₂) (hω.isChartChange_transition hO hr hs) x
  refine (congrArg (fun y => BilinearCoordinate.Coordinates.vec y i) key).trans ?_
  rw [BilinearCoordinate.Coordinates.vec_linearMap]
  simp only [BilinearCoordinate.matrixVec, transitionMatrix, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- On the integral scalar coordinate, the transition multiplies by
`ϖ^{scalarExponent r₁ s₁ r₂ s₂}`. -/
theorem scalar_integralCoordinatesEquiv_latticeTransition {r₁ s₁ r₂ s₂ : ℝ} (hr : r₁ ≤ r₂)
    (hs : s₁ ≤ s₂) (x : (hω.latticeModel hO r₂ s₂).integralSections) :
    ((hω.latticeChart hO r₁ s₁).integralCoordinatesEquiv
        (rationalPoints.map (hω.latticeTransition hO hr hs).hom x)).scalar =
      hω.integralUniformizer hO ^ (hω.scalarExponent r₁ s₁ r₂ s₂).toNat *
        ((hω.latticeChart hO r₂ s₂).integralCoordinatesEquiv x).scalar := by
  have key := (hω.latticeChart hO r₂ s₂).integralCoordinatesEquiv_chartHom
    (hω.latticeChart hO r₁ s₁) (hω.transitionMatrix hO r₁ r₂)
    (hω.transitionScalar hO r₁ s₁ r₂ s₂) (hω.isChartChange_transition hO hr hs) x
  refine (congrArg BilinearCoordinate.Coordinates.scalar key).trans ?_
  rw [BilinearCoordinate.Coordinates.scalar_linearMap]
  rfl

end IsRamifiedQuadraticValuation

end LatticeModel

end Langlands.GroupScheme.SU3Root
