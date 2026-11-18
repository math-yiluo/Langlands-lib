import Langlands.Representation.MatrixCoefficient.TwistedCosetSpace
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Topology.Algebra.OpenSubgroup

/-! # Hecke operators on the twisted `ℓ²` space of a coset space

Let `K` be an open subgroup of a group `G` and `J ⊇ K` a subgroup with `J = K · Z(G)`. Let
`ψ : J →* ℂ` be a unitary character that is trivial on `K`. For `g ∈ G` the subgroup
`heckeSub K g = K ∩ g K g⁻¹` has finite index `n` in `K` when `K` is compact. The Hecke
operator `hecke g` sends `F ∈ ℓ²(G ⧸ J)` to the function with lift

  `x ↦ n⁻¹ * ∑_{q ∈ K ⧸ heckeSub K g} lift F (x * q.out * g)`.

* `sum_mul_out_mul`: left multiplication by `k ∈ K` permutes these summands.
* `lift_heckeFun`: the right side is `ψ`-equivariant, so it is the lift of its values on the
  representatives.
* `tsum_enorm_heckeFun_le`: if `G ⧸ Z(G)` carries a left and right invariant Haar measure
  giving the image of `J` finite measure, the operator does not increase the `ℓ²` norm.
* `hecke`: the operator as a bounded operator, given that bound.
* `hecke_mem_centralizer`: it commutes with the left translations.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace Langlands.TwistedCoset

section Algebra

variable {G : Type*} [Group G] [TopologicalSpace G] (K : OpenSubgroup G)

/-- The subgroup of `k ∈ K` with `g⁻¹ * k * g ∈ K`, that is, `K ∩ g K g⁻¹` inside `K`. -/
def heckeSub (g : G) : Subgroup K where
  carrier := {k | g⁻¹ * (k : G) * g ∈ K}
  one_mem' := by
    show g⁻¹ * ((1 : K) : G) * g ∈ K
    rw [OneMemClass.coe_one, mul_one, inv_mul_cancel]
    exact K.one_mem
  mul_mem' := by
    intro a b ha hb
    show g⁻¹ * ((a * b : K) : G) * g ∈ K
    have h : g⁻¹ * ((a * b : K) : G) * g = (g⁻¹ * (a : G) * g) * (g⁻¹ * (b : G) * g) := by
      rw [MulMemClass.coe_mul]
      group
    rw [h]
    exact K.mul_mem ha hb
  inv_mem' := by
    intro a ha
    show g⁻¹ * ((a⁻¹ : K) : G) * g ∈ K
    have h : g⁻¹ * ((a⁻¹ : K) : G) * g = (g⁻¹ * (a : G) * g)⁻¹ := by
      rw [InvMemClass.coe_inv]
      group
    rw [h]
    exact K.inv_mem ha

theorem mem_heckeSub_iff (g : G) (k : K) : k ∈ heckeSub K g ↔ g⁻¹ * (k : G) * g ∈ K :=
  Iff.rfl

variable {K}

/-- Left multiplication by an element of `K` permutes the Hecke summands of a right
`K`-invariant function. -/
theorem sum_mul_out_mul {M : Type*} [AddCommMonoid M] (g : G) [Fintype (K ⧸ heckeSub K g)]
    (f : G → M) (hf : ∀ y : G, ∀ k ∈ K, f (y * k) = f y) (x : G) {k : G} (hk : k ∈ K) :
    ∑ q : K ⧸ heckeSub K g, f (x * k * (q.out : G) * g) =
      ∑ q : K ⧸ heckeSub K g, f (x * (q.out : G) * g) := by
  let k' : K := ⟨k, hk⟩
  calc ∑ q : K ⧸ heckeSub K g, f (x * k * (q.out : G) * g)
      = ∑ q : K ⧸ heckeSub K g, f (x * ((k' • q).out : G) * g) := by
        refine Finset.sum_congr rfl fun q _ => ?_
        have hq : k' • q = (QuotientGroup.mk (k' * q.out) : K ⧸ heckeSub K g) :=
          (MulAction.Quotient.mk_smul_out (heckeSub K g) k' q).symm
        obtain ⟨l, hl⟩ := QuotientGroup.mk_out_eq_mul (heckeSub K g) (k' * q.out)
        rw [hq, hl, MulMemClass.coe_mul, MulMemClass.coe_mul]
        have hmem : g⁻¹ * ((l : K) : G) * g ∈ K := l.2
        have h : x * ((k' : G) * (q.out : G) * ((l : K) : G)) * g =
            x * k * (q.out : G) * g * (g⁻¹ * ((l : K) : G) * g) := by
          simp only [k']
          group
        rw [h, hf _ _ hmem]
    _ = ∑ q : K ⧸ heckeSub K g, f (x * (q.out : G) * g) :=
        Equiv.sum_comp (MulAction.toPerm k' : Equiv.Perm (K ⧸ heckeSub K g))
          (fun q => f (x * (q.out : G) * g))

omit [TopologicalSpace G] in
/-- Moving a central element to the right end of a product. -/
theorem mul_mul_center_mul_mul (x k a g : G) {z : G} (hz : z ∈ Subgroup.center G) :
    x * (k * z) * a * g = x * k * a * g * z := by
  have hc : z * (a * g) = a * g * z := (Subgroup.mem_center_iff.mp hz (a * g)).symm
  calc x * (k * z) * a * g = x * k * (z * (a * g)) := by simp only [mul_assoc]
    _ = x * k * (a * g * z) := by rw [hc]
    _ = x * k * a * g * z := by simp only [mul_assoc]

variable (K) (J : Subgroup G) (ψ : J →* ℂ)

/-- The Hecke average `n⁻¹ * ∑_q lift F (x * q.out * g)`, as a function on `G`. -/
def heckeFun (g : G) [Fintype (K ⧸ heckeSub K g)] (F : G ⧸ J → ℂ) (x : G) : ℂ :=
  (Fintype.card (K ⧸ heckeSub K g) : ℂ)⁻¹ *
    ∑ q : K ⧸ heckeSub K g, lift J ψ F (x * (q.out : G) * g)

variable {K J ψ}
variable (hKJ : ∀ k ∈ K, k ∈ J) (hψK : ∀ (k : G) (hk : k ∈ K), ψ ⟨k, hKJ k hk⟩ = 1)
  (hZJ : Subgroup.center G ≤ J)
  (hJKZ : ∀ j ∈ J, ∃ k ∈ K, ∃ z ∈ Subgroup.center G, j = k * z)

include hψK in
/-- A lift is right `K`-invariant, since `ψ` is trivial on `K`. -/
theorem lift_mul_of_mem (F : G ⧸ J → ℂ) (y : G) {k : G} (hk : k ∈ K) :
    lift J ψ F (y * k) = lift J ψ F y := by
  rw [lift_mul J ψ F y (hKJ k hk), hψK k hk, mul_one]

include hψK hZJ hJKZ in
/-- The Hecke average is `ψ`-equivariant on the right. -/
theorem heckeFun_mul (g : G) [Fintype (K ⧸ heckeSub K g)] (F : G ⧸ J → ℂ) (x : G) {j : G}
    (hj : j ∈ J) : heckeFun K J ψ g F (x * j) = heckeFun K J ψ g F x * ψ ⟨j, hj⟩ := by
  obtain ⟨k, hk, z, hz, rfl⟩ := hJKZ j hj
  have hzJ : z ∈ J := hZJ hz
  have hψj : ψ ⟨k * z, hj⟩ = ψ ⟨z, hzJ⟩ := by
    rw [show (⟨k * z, hj⟩ : J) = ⟨k, hKJ k hk⟩ * ⟨z, hzJ⟩ from rfl, map_mul, hψK k hk,
      one_mul]
  have hterm : ∀ q : K ⧸ heckeSub K g,
      lift J ψ F (x * (k * z) * (q.out : G) * g) =
        lift J ψ F (x * k * (q.out : G) * g) * ψ ⟨z, hzJ⟩ := by
    intro q
    rw [mul_mul_center_mul_mul x k _ g hz, lift_mul J ψ F _ hzJ]
  unfold heckeFun
  rw [Finset.sum_congr rfl fun q _ => hterm q, ← Finset.sum_mul,
    sum_mul_out_mul g (lift J ψ F) (fun y k hk => lift_mul_of_mem hKJ hψK F y hk) x hk, hψj]
  ring

include hψK hZJ hJKZ in
/-- The Hecke average is the lift of its values on the representatives. -/
theorem lift_heckeFun (g : G) [Fintype (K ⧸ heckeSub K g)] (F : G ⧸ J → ℂ) :
    lift J ψ (fun α => heckeFun K J ψ g F α.out) = heckeFun K J ψ g F :=
  lift_restrict J ψ _ fun x _ hj => heckeFun_mul hKJ hψK hZJ hJKZ g F x hj

end Algebra

section Mean

/-- The square of a mean is at most the mean of the squares. -/
theorem enorm_mean_sq_le {ι : Type*} [Fintype ι] [Nonempty ι] (a : ι → ℂ) :
    ‖(Fintype.card ι : ℂ)⁻¹ * ∑ i, a i‖ₑ ^ 2 ≤
      (Fintype.card ι : ℝ≥0∞)⁻¹ * ∑ i, ‖a i‖ₑ ^ 2 := by
  have hn : (Fintype.card ι : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hnt : (Fintype.card ι : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top _
  have hnC : (Fintype.card ι : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have h1 : ‖(Fintype.card ι : ℂ)⁻¹‖ₑ = (Fintype.card ι : ℝ≥0∞)⁻¹ := by
    rw [enorm_inv hnC, ← ofReal_norm, Complex.norm_natCast, ENNReal.ofReal_natCast]
  have hcs : (∑ i, ‖a i‖ₑ) ^ 2 ≤ (Fintype.card ι : ℝ≥0∞) * ∑ i, ‖a i‖ₑ ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => ‖a i‖₊)
    simp only [Finset.card_univ] at h
    simp only [enorm_eq_nnnorm]
    exact_mod_cast h
  calc ‖(Fintype.card ι : ℂ)⁻¹ * ∑ i, a i‖ₑ ^ 2
      = ((Fintype.card ι : ℝ≥0∞)⁻¹) ^ 2 * ‖∑ i, a i‖ₑ ^ 2 := by
        rw [enorm_mul, h1, mul_pow]
    _ ≤ ((Fintype.card ι : ℝ≥0∞)⁻¹) ^ 2 * (∑ i, ‖a i‖ₑ) ^ 2 := by
        gcongr
        exact enorm_sum_le _ _
    _ ≤ ((Fintype.card ι : ℝ≥0∞)⁻¹) ^ 2 * ((Fintype.card ι : ℝ≥0∞) * ∑ i, ‖a i‖ₑ ^ 2) := by
        gcongr
    _ = (Fintype.card ι : ℝ≥0∞)⁻¹ * ∑ i, ‖a i‖ₑ ^ 2 := by
        rw [sq, mul_assoc, ← mul_assoc _ (Fintype.card ι : ℝ≥0∞),
          ENNReal.inv_mul_cancel hn hnt, one_mul]

end Mean

section Measure

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {K : OpenSubgroup G} {J : Subgroup G} {ψ : J →* ℂ}
  (hψ : ∀ j, ‖ψ j‖ = 1)
  (hKJ : ∀ k ∈ K, k ∈ J) (hψK : ∀ (k : G) (hk : k ∈ K), ψ ⟨k, hKJ k hk⟩ = 1)
  (hZJ : Subgroup.center G ≤ J) (hJ : IsOpen (J : Set G))
  (hJKZ : ∀ j ∈ J, ∃ k ∈ K, ∃ z ∈ Subgroup.center G, j = k * z)
  [MeasurableSpace (G ⧸ Subgroup.center G)] [BorelSpace (G ⧸ Subgroup.center G)]
  (μ : Measure (G ⧸ Subgroup.center G)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]

include hψ hKJ hZJ hJ hJKZ in
/-- The Hecke average does not increase the `ℓ²` norm. -/
theorem tsum_enorm_heckeFun_le (hfin : μ (CentralCoset.centralImage J) ≠ ∞)
    (g : G) [Fintype (K ⧸ heckeSub K g)] (F : L2 J) :
    ∑' α : G ⧸ J, ‖heckeFun K J ψ g F α.out‖ₑ ^ 2 ≤ ‖F‖ₑ ^ 2 := by
  have hne : Nonempty (K ⧸ heckeSub K g) := ⟨QuotientGroup.mk 1⟩
  set n := Fintype.card (K ⧸ heckeSub K g) with hn
  have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hnt : (n : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top _
  let Ψ : G → ℝ≥0∞ := fun x => ‖lift J ψ F x‖ₑ ^ 2
  have hΨ : ∀ x, ∀ j ∈ J, Ψ (x * j) = Ψ x := by
    intro x j hj
    simp only [Ψ]
    rw [lift_mul J ψ _ x hj, enorm_mul, enorm_eq_one_of_norm_eq_one (hψ _), mul_one]
  let Φ : G → ℝ≥0∞ := fun x => ∑ q : K ⧸ heckeSub K g, Ψ (x * (q.out : G) * g)
  have hΦ : ∀ x, ∀ j ∈ J, Φ (x * j) = Φ x := by
    intro x j hj
    obtain ⟨k, hk, z, hz, rfl⟩ := hJKZ j hj
    have hterm : ∀ q : K ⧸ heckeSub K g,
        Ψ (x * (k * z) * (q.out : G) * g) = Ψ (x * k * (q.out : G) * g) := by
      intro q
      rw [mul_mul_center_mul_mul x k _ g hz, hΨ _ z (hZJ hz)]
    simp only [Φ]
    rw [Finset.sum_congr rfl fun q _ => hterm q]
    exact sum_mul_out_mul g Ψ (fun y k hk => hΨ y k (hKJ k hk)) x hk
  have hΨc : ∀ x, ∀ z ∈ Subgroup.center G, Ψ (x * z) = Ψ x := fun x z hz => hΨ x z (hZJ hz)
  have hmeas : ∀ h : G, Measurable fun q : G ⧸ Subgroup.center G => Ψ (q.out * h) := by
    intro h
    have heq : (fun q : G ⧸ Subgroup.center G => Ψ (q.out * h)) =
        (fun q : G ⧸ Subgroup.center G => Ψ q.out) ∘
          (fun q => q * (QuotientGroup.mk h : G ⧸ Subgroup.center G)) := by
      funext q
      obtain ⟨z, hz, hout⟩ :=
        CentralCoset.exists_out_mk_eq_mul_center (q.out * h)
      simp only [Function.comp_apply]
      rw [show q * (QuotientGroup.mk h : G ⧸ Subgroup.center G) =
          QuotientGroup.mk (q.out * h) by
        rw [QuotientGroup.mk_mul, QuotientGroup.out_eq'], hout, hΨc _ z hz]
    rw [heq]
    exact (CentralCoset.measurable_out J hZJ hJ Ψ hΨ).comp
      (continuous_id.mul continuous_const).measurable
  have hint : μ (CentralCoset.centralImage J) * ∑' α : G ⧸ J, Φ α.out =
      μ (CentralCoset.centralImage J) * ((n : ℝ≥0∞) * ∑' α : G ⧸ J, Ψ α.out) := by
    rw [← CentralCoset.lintegral_out_eq_mul_tsum J hZJ hJ μ Φ hΦ]
    simp only [Φ]
    rw [lintegral_finsetSum _ fun q _ => by
      simpa only [mul_assoc] using hmeas ((q.out : G) * g)]
    have hq : ∀ q : K ⧸ heckeSub K g,
        ∫⁻ q' : G ⧸ Subgroup.center G, Ψ (q'.out * (q.out : G) * g) ∂μ =
          ∫⁻ q' : G ⧸ Subgroup.center G, Ψ q'.out ∂μ := by
      intro q
      simp only [mul_assoc]
      exact CentralCoset.lintegral_out_mul_eq μ Ψ hΨc _
    rw [Finset.sum_congr rfl fun q _ => hq q, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      CentralCoset.lintegral_out_eq_mul_tsum J hZJ hJ μ Ψ hΨ, ← hn]
    ring
  have hsum : ∑' α : G ⧸ J, Φ α.out = (n : ℝ≥0∞) * ∑' α : G ⧸ J, Ψ α.out :=
    (ENNReal.mul_right_inj (CentralCoset.centralImage_measure_ne_zero J hZJ hJ μ) hfin).mp hint
  calc ∑' α : G ⧸ J, ‖heckeFun K J ψ g F α.out‖ₑ ^ 2
      ≤ ∑' α : G ⧸ J, (n : ℝ≥0∞)⁻¹ * Φ α.out :=
        ENNReal.tsum_le_tsum fun α => enorm_mean_sq_le _
    _ = (n : ℝ≥0∞)⁻¹ * ((n : ℝ≥0∞) * ∑' α : G ⧸ J, Ψ α.out) := by
        rw [ENNReal.tsum_mul_left, hsum]
    _ = ∑' α : G ⧸ J, Ψ α.out := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hn0 hnt, one_mul]
    _ = ‖F‖ₑ ^ 2 := by
        rw [Langlands.Analysis.lp_two_enorm_sq_eq_tsum]
        simp only [Ψ, lift_out]

end Measure

section Operator

variable {G : Type*} [Group G] [TopologicalSpace G]
  {K : OpenSubgroup G} {J : Subgroup G} {ψ : J →* ℂ} (g : G) [Fintype (K ⧸ heckeSub K g)]
  (hb : ∀ F : L2 J, ∑' α : G ⧸ J, ‖heckeFun K J ψ g F α.out‖ₑ ^ 2 ≤ ‖F‖ₑ ^ 2)

include hb in
theorem memℓp_heckeFun (F : L2 J) : Memℓp (fun α : G ⧸ J => heckeFun K J ψ g F α.out) 2 :=
  Langlands.Analysis.memℓp_two_of_tsum_enorm_ne_top _
    (ne_top_of_le_ne_top (ENNReal.pow_ne_top enorm_ne_top) (hb F))

/-- The Hecke operator as a linear map on `ℓ²(G ⧸ J)`, given the norm bound `hb`. -/
def heckeₗ : L2 J →ₗ[ℂ] L2 J where
  toFun F := ⟨fun α => heckeFun K J ψ g F α.out, memℓp_heckeFun g hb F⟩
  map_add' F F' := by
    ext α
    change heckeFun K J ψ g (⇑(F + F')) α.out =
      heckeFun K J ψ g (⇑F) α.out + heckeFun K J ψ g (⇑F') α.out
    simp only [heckeFun, lp.coeFn_add, lift_add, Finset.sum_add_distrib, mul_add]
  map_smul' c F := by
    ext α
    change heckeFun K J ψ g (⇑(c • F)) α.out = c * heckeFun K J ψ g (⇑F) α.out
    simp only [heckeFun, lp.coeFn_smul, lift_smul, ← Finset.mul_sum]
    ring

/-- The Hecke operator as a bounded operator on `ℓ²(G ⧸ J)`, given the norm bound `hb`. -/
def hecke : L2 J →L[ℂ] L2 J :=
  (heckeₗ g hb).mkContinuous 1 fun F => by
    rw [one_mul]
    apply norm_le_of_enorm_sq_le
    exact (Langlands.Analysis.lp_two_enorm_sq_eq_tsum (heckeₗ g hb F)).trans_le (hb F)
where
  norm_le_of_enorm_sq_le {x y : L2 J} (h : ‖x‖ₑ ^ 2 ≤ ‖y‖ₑ ^ 2) : ‖x‖ ≤ ‖y‖ :=
    enorm_le_iff_norm_le.mp ((ENNReal.pow_le_pow_left_iff two_ne_zero).mp h)

theorem hecke_apply (F : L2 J) (α : G ⧸ J) : hecke g hb F α = heckeFun K J ψ g F α.out :=
  rfl

variable (hψ : ∀ j, ‖ψ j‖ = 1)
  (hKJ : ∀ k ∈ K, k ∈ J) (hψK : ∀ (k : G) (hk : k ∈ K), ψ ⟨k, hKJ k hk⟩ = 1)
  (hZJ : Subgroup.center G ≤ J)
  (hJKZ : ∀ j ∈ J, ∃ k ∈ K, ∃ z ∈ Subgroup.center G, j = k * z)

include hψK hZJ hJKZ in
theorem lift_hecke (F : L2 J) : lift J ψ (hecke g hb F) = heckeFun K J ψ g F :=
  lift_heckeFun hKJ hψK hZJ hJKZ g F

include hψK hZJ hJKZ in
/-- The Hecke operators commute with the left translations. -/
theorem hecke_mem_centralizer :
    hecke g hb ∈ StarSubalgebra.centralizer ℂ (translates hψ) := by
  rw [mem_centralizer_translates_iff]
  intro h F
  ext α
  rw [translate_apply, translateₗ_apply, lift_hecke g hb hKJ hψK hZJ hJKZ, hecke_apply,
    translate_apply]
  unfold heckeFun
  congr 1
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [lift_translateₗ]
  simp only [mul_assoc]

end Operator

end Langlands.TwistedCoset
