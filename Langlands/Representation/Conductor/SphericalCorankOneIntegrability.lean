import Langlands.Representation.Conductor.EssentialConductorAssembly
import Langlands.Representation.Conductor.WhittakerTorusBound
import Langlands.Representation.Conductor.SphericalCellMeasureBound
import Langlands.Representation.Conductor.SatakeSchurBound
import Langlands.Representation.Conductor.SphericalCompact
import Langlands.Representation.Conductor.SphericalAnalysis
import Langlands.Representation.Conductor.SphericalDegree

/-!
# Absolute convergence of the corank-one integrals against `W(x; ψ̄)`

For an admissible `π` of `GL_(n+2)(F)`, a vector `w` of a Whittaker model and a Satake
parameter `x`, the corank-one integral `Ψ(s, w, W(x; ψ̄))` converges absolutely for
`Re s` large. On the Iwasawa cell of `ϖ^λ` the integrand is bounded by the torus bound
for `w`, the Schur bound for `W(x; ψ̄)` and `q^(-(∑ λ) (Re s - 1/2))`; the cell masses
grow at most exponentially, and the support condition `λ` antitone with
`λ_last ≥ b` makes the resulting series a product of geometric series.
-/

noncomputable section

namespace Langlands.Conductor

open MeasureTheory Langlands.GeneralLinear Langlands.Whittaker Langlands.HarmonicAnalysis
open Langlands.RankinSelberg Langlands.QuotientIntegration Langlands.GeneralLinear.Iwasawa
open Langlands.GeneralLinear.Spherical

universe uF uV

/-! ### Summability of products of one-variable series -/

section Summable

/-- A product of a summable nonnegative function of each coordinate is summable on
`Fin (m + 1) → ℤ`. -/
theorem summable_prod_fin {g : ℤ → ℝ} (hg : Summable g) (hg0 : ∀ z, 0 ≤ g z) :
    ∀ m : ℕ, Summable (fun lam : Fin (m + 1) → ℤ => ∏ i, g (lam i))
  | 0 => by
    let e : (Fin 1 → ℤ) ≃ ℤ := Equiv.funUnique (Fin 1) ℤ
    have he : (fun lam : Fin 1 → ℤ => ∏ i, g (lam i)) = g ∘ e := by
      funext lam
      simp [e]
    rw [he]
    exact e.summable_iff.mpr hg
  | m + 1 => by
    let e : (Fin (m + 1 + 1) → ℤ) ≃ ℤ × (Fin (m + 1) → ℤ) :=
      (Fin.consEquiv (fun _ : Fin (m + 1 + 1) => ℤ)).symm
    have h1 : Summable (fun lam : Fin (m + 1) → ℤ => ∏ i, g (lam i)) :=
      summable_prod_fin hg hg0 m
    have hg' : (0 : ℤ → ℝ) ≤ g := fun z => hg0 z
    have h1' : (0 : (Fin (m + 1) → ℤ) → ℝ) ≤ fun lam => ∏ i, g (lam i) :=
      fun lam => Finset.prod_nonneg fun i _ => hg0 _
    have hprod : Summable (fun p : ℤ × (Fin (m + 1) → ℤ) => g p.1 * ∏ i, g (p.2 i)) :=
      Summable.mul_of_nonneg (f := g) (g := fun lam : Fin (m + 1) → ℤ => ∏ i, g (lam i))
        hg h1 hg' h1'
    have he : (fun lam : Fin (m + 1 + 1) → ℤ => ∏ i, g (lam i)) =
        (fun p : ℤ × (Fin (m + 1) → ℤ) => g p.1 * ∏ i, g (p.2 i)) ∘ e := by
      funext lam
      rw [Fin.prod_univ_succ]
      rfl
    rw [he]
    exact e.summable_iff.mpr hprod

/-- A one-sided geometric series on `ℤ`. -/
theorem summable_shifted_geometric (b : ℤ) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (K : ℝ) :
    Summable (fun z : ℤ => if b ≤ z then K * ρ ^ z else 0) := by
  let f : ℤ → ℝ := fun z => if b ≤ z then K * ρ ^ z else 0
  let i : ℕ → ℤ := fun k => b + k
  have hi : Function.Injective i := fun x y h => by
    simp only [i] at h
    exact_mod_cast add_left_cancel h
  have hzero : ∀ z ∉ Set.range i, f z = 0 := by
    intro z hz
    have : ¬ b ≤ z := by
      intro hbz
      exact hz ⟨(z - b).toNat, by simp only [i]; omega⟩
    simp only [f, this, ite_false]
  have hcomp : f ∘ i = fun k : ℕ => (K * ρ ^ b) * ρ ^ k := by
    funext k
    simp only [Function.comp_apply, f, i, le_add_iff_nonneg_right, Nat.cast_nonneg, ite_true]
    rw [zpow_add₀ hρ0.ne', zpow_natCast]
    ring
  change Summable f
  rw [← hi.summable_iff hzero, hcomp]
  exact (summable_geometric_of_lt_one hρ0.le hρ1).mul_left _

end Summable

/-! ### Torus identities in the corank-one embedding -/

section Torus

variable {F : Type uF} [Field F] {n : ℕ}

/-- `diag(ϖ^λ, 1)` is the torus element of `GL_(n+2)` with exponent `(λ, 0)`. -/
theorem rankInclusion_torus_succ (ϖ : Fˣ) (lam : Fin (n + 1) → ℤ) :
    rankInclusion 1 (torus ϖ lam) = torus ϖ (Fin.snoc lam 0) := by
  apply Units.ext
  ext i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp [torus_val, Matrix.diagonal_apply, rankInclusion_castSucc_castSucc,
      rankInclusion_castSucc_last, rankInclusion_last_castSucc, rankInclusion_last_last,
      Ne.symm (Fin.castSucc_ne_last _)]

/-- Splitting off the last exponent. -/
theorem torus_snoc_split (ϖ : Fˣ) (lam : Fin (n + 1) → ℤ) (c : ℤ) :
    torus ϖ (Fin.snoc lam 0 : Fin (n + 1 + 1) → ℤ) =
      torus ϖ (Fin.snoc lam c) * torus ϖ (Fin.snoc (0 : Fin (n + 1) → ℤ) (-c)) := by
  rw [← torus_add]
  congr 1
  funext j
  induction j using Fin.lastCases with
  | last => simp
  | cast j => simp

/-- A torus element supported on the last coordinate commutes with `diag(k, 1)`. -/
theorem torus_last_commute (ϖ : Fˣ) (e : ℤ) (k : Langlands.GeneralLinear (n + 1) F) :
    torus ϖ (Fin.snoc (0 : Fin (n + 1) → ℤ) e) * rankInclusion 1 k =
      rankInclusion 1 k * torus ϖ (Fin.snoc (0 : Fin (n + 1) → ℤ) e) := by
  apply Units.ext
  ext i j
  simp only [Units.val_mul, torus_val, Matrix.diagonal_mul, Matrix.mul_diagonal]
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp [rankInclusion_castSucc_castSucc, rankInclusion_castSucc_last,
      rankInclusion_last_castSucc, rankInclusion_last_last]

/-- The snoc of an antitone exponent by a lower value is antitone. -/
theorem antitone_snoc {lam : Fin (n + 1) → ℤ} (hlam : Antitone lam) {c : ℤ}
    (hc : c ≤ lam (Fin.last n)) : Antitone (Fin.snoc lam c : Fin (n + 1 + 1) → ℤ) := by
  intro i j hij
  induction j using Fin.lastCases with
  | last =>
    induction i using Fin.lastCases with
    | last => exact le_rfl
    | cast i =>
      simp only [Fin.snoc_last, Fin.snoc_castSucc]
      exact le_trans hc (hlam (Fin.le_last i))
  | cast j =>
    induction i using Fin.lastCases with
    | last =>
      exact absurd hij (not_le.mpr (Fin.castSucc_lt_last j))
    | cast i =>
      simp only [Fin.snoc_castSucc]
      exact hlam (Fin.castSucc_le_castSucc_iff.mp hij)

theorem sum_natAbs_snoc (lam : Fin (n + 1) → ℤ) (c : ℤ) :
    ∑ j, ((Fin.snoc lam c : Fin (n + 1 + 1) → ℤ) j).natAbs =
      ∑ i, (lam i).natAbs + c.natAbs := by
  rw [Fin.sum_univ_castSucc]
  simp

end Torus

/-! ### Torus bound for a model vector on the corank-one embedding -/

section ModelBound

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable [IsNonarchimedeanLocalField F] {n : ℕ}
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (π : Representation ℂ (Langlands.GeneralLinear ((n + 1) + 1) F) V)
variable (hπ : IsAdmissible π) {ψ : UnitaryAdditiveCharacter F} (hψ : HasIntegerConductor ψ)
variable (ℓ : glFunctionals ψ (n + 1) π) {ϖ : Fˣ}
variable (hϖ : IsUniformizingElement (ValuativeRel.valuation F) ϖ)

include hπ hψ hϖ in
/-- For a model vector `w` there are `b`, `C`, `A` such that `w(diag(ϖ^λ k, 1))` vanishes
unless `b ≤ λ_last`, and is bounded by `C A^(∑ |λ_i|)` for antitone `λ` and integral `k`. -/
theorem model_corankOne_torus_bound (w : (coefficientModel π ℓ).toSubmodule) :
    ∃ b : ℤ, ∃ C A : ℝ, 0 < C ∧ 1 ≤ A ∧
      ∀ (lam : Fin (n + 1) → ℤ) (k : Langlands.GeneralLinear (n + 1) F),
        k ∈ integralSubgroup (ValuativeRel.valuation F).integer n →
          (w.val.val (rankInclusion 1 (torus ϖ lam * k)) ≠ 0 → b ≤ lam (Fin.last n)) ∧
          (Antitone lam → ‖w.val.val (rankInclusion 1 (torus ϖ lam * k))‖ ≤
            C * A ^ (∑ i, (lam i).natAbs)) := by
  classical
  obtain ⟨v, hv⟩ := w.property
  have hW : ∀ g, w.val.val g = ℓ.val (π g v) := by
    intro g
    rw [← hv]
    rfl
  obtain ⟨b, hb⟩ := model_corankOne_last_exponent_lower_bound hϖ π hπ.1 ψ ℓ hψ w
  set b0 : ℤ := min b 0 with hb0
  let vc : ℤ → V := fun c => π (torus ϖ (Fin.snoc (0 : Fin (n + 1) → ℤ) (-c))) v
  have hlev : ∀ c : ℤ, ∃ a : ℕ, 0 < a ∧
      vc c ∈ fixedVectors π (principalLevelOpenSubgroup F (n + 1) a).toSubgroup := by
    intro c
    obtain ⟨U, hU⟩ := hπ.1 (vc c)
    obtain ⟨a, ha, haU⟩ :=
      exists_pos_principalLevelOpenSubgroup_subset F (n + 1) U.mem_nhds_one
    exact ⟨a, ha, fun κ => hU ⟨κ.val, haU κ.property⟩⟩
  choose a ha hav using hlev
  let I : Finset ℤ := Finset.Icc b0 0
  let A0 : ℕ := 1 + ∑ c ∈ I, a c
  have hA0 : 0 < A0 := by omega
  have hvA : ∀ c ∈ I,
      vc c ∈ fixedVectors π (principalLevelOpenSubgroup F (n + 1) A0).toSubgroup := by
    intro c hc κ
    have hle : a c ≤ A0 := by
      have := Finset.single_le_sum (f := a) (fun _ _ => Nat.zero_le _) hc
      omega
    exact hav c ⟨κ.val, principalLevelSubgroup_antitone F (n + 1) hle κ.property⟩
  let K0 := principalLevelOpenSubgroup F (n + 1) 0
  let S : Set V := ⋃ c ∈ I, Set.range
    (fun k : integralSubgroup (ValuativeRel.valuation F).integer n =>
      π (rankInclusion 1 k.val) (vc c))
  have hRK : ∀ k : integralSubgroup (ValuativeRel.valuation F).integer n,
      rankInclusion 1 k.val ∈ Iwasawa.integralRange (ValuativeRel.valuation F) (n + 1 + 1) :=
    fun k => rankInclusion_mem (ValuativeRel.valuation F) k.property
  have hSfin : S.Finite := by
    apply Set.Finite.biUnion I.finite_toSet
    intro c _
    have hfin := Compact.finite_orbit_of_smooth π hπ.1 K0
      (isCompact_principalLevelOpenSubgroup F (n + 1) 0) (vc c)
    have hsub : Set.range (fun k : integralSubgroup (ValuativeRel.valuation F).integer n =>
        π (rankInclusion 1 k.val) (vc c)) ⊆
          Compact.orbit (π.comp K0.toSubgroup.subtype) (vc c) := by
      rintro _ ⟨k, rfl⟩
      refine ⟨⟨rankInclusion 1 k.val, ?_⟩, rfl⟩
      change rankInclusion 1 k.val ∈ principalLevelSubgroup F (n + 1) 0
      rw [principalLevelSubgroup_zero]
      exact hRK k
    exact (Set.finite_coe_iff.mp hfin).subset hsub
  have hSK : S ⊆ fixedVectors π (principalLevelOpenSubgroup F (n + 1) A0).toSubgroup := by
    intro u hu
    obtain ⟨c, hc, hu⟩ := Set.mem_iUnion₂.mp hu
    obtain ⟨k, rfl⟩ := hu
    intro κ
    have hconj := conj_mem_rankPrincipalLevel (inv_mem (hRK k)) κ.property
    rw [inv_inv] at hconj
    change π κ.val (π (rankInclusion 1 k.val) (vc c)) = π (rankInclusion 1 k.val) (vc c)
    calc
      π κ.val (π (rankInclusion 1 k.val) (vc c)) =
          π (rankInclusion 1 k.val)
            (π ((rankInclusion 1 k.val)⁻¹ * κ.val * rankInclusion 1 k.val) (vc c)) := by
        simp only [← Module.End.mul_apply, ← map_mul]
        congr 2
        group
      _ = π (rankInclusion 1 k.val) (vc c) := by
        have hfix : π ((rankInclusion 1 k.val)⁻¹ * κ.val * rankInclusion 1 k.val) (vc c) =
            vc c := hvA c hc ⟨_, hconj⟩
        rw [hfix]
  obtain ⟨A, hA, C, hC, hbound⟩ :=
    whittaker_torus_bound_finite (m := n + 1) π hϖ.1.le hA0 hψ.1 hπ ℓ hSfin hSK
  refine ⟨b, C * A ^ b0.natAbs, A, by positivity, hA, fun lam k hk =>
    ⟨fun hne => hb lam k hk hne, fun hlam => ?_⟩⟩
  by_cases hz : w.val.val (rankInclusion 1 (torus ϖ lam * k)) = 0
  · rw [hz, norm_zero]
    positivity
  have hbl := hb lam k hk hz
  set c : ℤ := min (lam (Fin.last n)) 0 with hc
  have hcI : c ∈ I := Finset.mem_Icc.mpr ⟨by omega, min_le_right _ _⟩
  have hdecomp : rankInclusion 1 (torus ϖ lam * k) =
      torus ϖ (Fin.snoc lam c) *
        (rankInclusion 1 k * torus ϖ (Fin.snoc (0 : Fin (n + 1) → ℤ) (-c))) := by
    rw [map_mul, rankInclusion_torus_succ, torus_snoc_split ϖ lam c, mul_assoc,
      torus_last_commute]
  have hu : π (rankInclusion 1 k) (vc c) ∈ S :=
    Set.mem_iUnion₂.mpr ⟨c, hcI, ⟨⟨k, hk⟩, rfl⟩⟩
  have hμ : Antitone (Fin.snoc lam c : Fin (n + 1 + 1) → ℤ) :=
    antitone_snoc hlam (min_le_left _ _)
  have hval : w.val.val (rankInclusion 1 (torus ϖ lam * k)) =
      ℓ.val (π (torus ϖ (Fin.snoc lam c)) (π (rankInclusion 1 k) (vc c))) := by
    rw [hW, hdecomp, map_mul, Module.End.mul_apply, map_mul, Module.End.mul_apply]
  rw [hval]
  have hcb : c.natAbs ≤ b0.natAbs := by omega
  calc
    ‖ℓ.val (π (torus ϖ (Fin.snoc lam c)) (π (rankInclusion 1 k) (vc c)))‖ ≤
        C * A ^ (∑ j, ((Fin.snoc lam c : Fin (n + 1 + 1) → ℤ) j).natAbs) :=
      hbound _ hu _ hμ
    _ = C * (A ^ (∑ i, (lam i).natAbs) * A ^ c.natAbs) := by
      rw [sum_natAbs_snoc, pow_add]
    _ ≤ C * (A ^ (∑ i, (lam i).natAbs) * A ^ b0.natAbs) := by
      gcongr
    _ = C * A ^ b0.natAbs * A ^ (∑ i, (lam i).natAbs) := by ring

end ModelBound

/-! ### Local constancy of the integrand -/

section LocalConstancy

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable [IsNonarchimedeanLocalField F] {n : ℕ}

/-- A function on `GL_(n+1)(F)` right invariant under `GL_(n+1)(O)` is locally constant. -/
theorem isLocallyConstant_of_right_integral {A : Type*}
    (f : Langlands.GeneralLinear (n + 1) F → A)
    (hf : ∀ (g k : Langlands.GeneralLinear (n + 1) F),
      k ∈ integralSubgroup (ValuativeRel.valuation F).integer n → f (g * k) = f g) :
    IsLocallyConstant f := by
  apply (IsLocallyConstant.iff_exists_open _).2
  intro g
  refine ⟨(fun h : Langlands.GeneralLinear (n + 1) F => g⁻¹ * h) ⁻¹'
      (integralSubgroup (ValuativeRel.valuation F).integer n :
        Set (Langlands.GeneralLinear (n + 1) F)),
    isOpen_integralSubgroup'.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
  · change g⁻¹ * g ∈ integralSubgroup (ValuativeRel.valuation F).integer n
    rw [inv_mul_cancel]
    exact one_mem _
  · intro h hh
    simpa only [mul_inv_cancel_left] using hf g (g⁻¹ * h) hh

/-- Local constancy descends to the left-unipotent quotient. -/
theorem isLocallyConstant_quotient_of_pullback {A : Type*}
    (f : LeftUnipotentQuotient n F → A)
    (hf : IsLocallyConstant
      (fun g => f (leftQuotientMap (upperUnipotent (n + 1) F) g))) :
    IsLocallyConstant f := by
  intro S
  exact (leftQuotient_isOpenQuotientMap (upperUnipotent (n + 1) F)
    ).isQuotientMap.isCoinducing.isOpen_preimage.mp (hf S)

end LocalConstancy

/-! ### Convergence -/

section Main

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable [IsNonarchimedeanLocalField F] {n : ℕ}
variable [MeasurableSpace (Langlands.GeneralLinear (n + 1) F)]
  [BorelSpace (Langlands.GeneralLinear (n + 1) F)]
variable [MeasurableSpace (upperUnipotent (n + 1) F)] [BorelSpace (upperUnipotent (n + 1) F)]
variable [MeasurableSpace (LeftUnipotentQuotient n F)] [MeasurableSpace (LeftUnipotentQuotient 0 F)]
variable {q : ℕ} {ψ : UnitaryAdditiveCharacter F} {abv : AbsoluteValue F ℝ} {ϖ : Fˣ}
  {μ : Measure (LeftUnipotentQuotient n F)}
variable (h : IsJacquetNormalization q ψ abv ϖ μ)
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (π : Representation ℂ (Langlands.GeneralLinear ((n + 1) + 1) F) V)

include h in
/-- The corank-one integrand against `W(x; ψ̄)` at a point of the Iwasawa cell of `ϖ^λ`. -/
theorem corankOneIntegrand_torus_mul (W : WhittakerFunctions ψ (n + 1))
    (x : Fin (n + 1) → ℂˣ) (s : ℂ) (lam : Fin (n + 1) → ℤ)
    {k : Langlands.GeneralLinear (n + 1) F}
    (hk : k ∈ integralSubgroup (ValuativeRel.valuation F).integer n) :
    corankOneIntegrand ψ abv W (inverseSphericalWhittaker h.conductor.1 h.uniformizer q x) s
        (Quotient.mk _ (torus ϖ lam * k)) =
      W.val (rankInclusion 1 (torus ϖ lam * k)) *
        (if Antitone lam then halfModulus q lam * satakeSchur x lam else 0) *
        ((q : ℂ) ^ (-(s - 1 / 2))) ^ (∑ i, lam i) := by
  have hq0 : 0 < q := lt_trans zero_lt_one (IsJacquetNormalization.one_lt_q h)
  rw [corankOneIntegrand_mk, inverseSphericalWhittaker_mul_integral _ _ _ _ _ hk,
    inverseSphericalWhittaker_apply,
    sphericalWhittaker_torus _ _ _ (isIntegrallyTrivial_inverseStandardCharacter h.conductor.1 n),
    determinantWeight_eq_degree_power abv h.uniformizer h.abv_unit q hq0 h.abv_uniformizer,
    exponent_mul_integral h.uniformizer _ hk, exponent_torus]

include h in
/-- The corank-one integrand of a smooth model vector against `W(x; ψ̄)` is continuous. -/
theorem corankOneIntegrand_model_continuous (hπ : IsSmooth π) {ℓ : glFunctionals ψ (n + 1) π}
    (w : (coefficientModel π ℓ).toSubmodule) (x : Fin (n + 1) → ℂˣ) (s : ℂ) :
    Continuous (corankOneIntegrand ψ abv w.val
      (inverseSphericalWhittaker h.conductor.1 h.uniformizer q x) s) := by
  obtain ⟨v, hv⟩ := w.property
  have hWv : w.val.val = matrixCoefficient π ℓ.val v := by
    rw [← hv]
    rfl
  apply IsLocallyConstant.continuous
  apply isLocallyConstant_quotient_of_pullback
  have h1 : IsLocallyConstant (fun g : Langlands.GeneralLinear (n + 1) F =>
      w.val.val (rankInclusion 1 g)) := by
    rw [hWv]
    exact (matrixCoefficient_isLocallyConstant π ℓ.val v (hπ v)).comp_continuous
      (rankInclusionContinuous (R := F) 1).continuous
  have h2 : IsLocallyConstant
      (inverseSphericalWhittaker h.conductor.1 h.uniformizer q x).val :=
    isLocallyConstant_of_right_integral _
      (fun g k hk => inverseSphericalWhittaker_mul_integral _ _ _ _ _ hk)
  have h3 := determinantWeight_isLocallyConstant (n := n) abv h.abv_unit (s - 1 / 2)
  exact (h1.mul h2).mul h3

/-- Products of integral powers of a nonzero real number. -/
theorem prod_real_zpow_eq {ι : Type*} (r : ℝ) (hr : r ≠ 0) (t : Finset ι) (f : ι → ℤ) :
    ∏ i ∈ t, r ^ f i = r ^ (∑ i ∈ t, f i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ hr]

include h in
/-- **Absolute convergence (clause 1).** For an admissible `π`, every vector `w` of the
model of `ℓ` and every Satake parameter `x`, the corank-one integral of `w` against
`W(x; ψ̄)` converges absolutely on a right half-plane. -/
theorem corankOneConverges_inverseSphericalWhittaker (hπ : IsAdmissible π)
    (ℓ : glFunctionals ψ (n + 1) π) (w : (coefficientModel π ℓ).toSubmodule)
    (x : Fin (n + 1) → ℂˣ) :
    ∃ a : ℝ, ∀ s : ℂ, a < s.re → CorankOneConverges ψ abv μ w.val
      (inverseSphericalWhittaker h.conductor.1 h.uniformizer q x) s := by
  classical
  let : BorelSpace (LeftUnipotentQuotient n F) := h.borel
  have hq1 : 1 < q := IsJacquetNormalization.one_lt_q h
  have hq0 : 0 < q := lt_trans zero_lt_one hq1
  have hq1' : (1 : ℝ) < q := by exact_mod_cast hq1
  obtain ⟨b, Cw, Aw, hCw, hAw, hW⟩ :=
    model_corankOne_torus_bound π hπ h.conductor ℓ h.uniformizer w
  obtain ⟨Cx, Bx, hCx, hBx, hX⟩ := exists_satakeSchur_bound q hq1.le x
  obtain ⟨c, hc1, hcell⟩ :=
    exists_sphericalCell_measure_le h.uniformizer (μ := μ) h.measure.right_invariant
  set M0 : ℝ := μ.real (sphericalCell h.uniformizer 0) with hM0
  have hM00 : 0 ≤ M0 := measureReal_nonneg
  have hc1' : (1 : ℝ) ≤ c := by exact_mod_cast hc1
  set D : ℝ := Aw * Bx * c with hD
  have hD1 : 1 ≤ D := by
    have h1 : 1 ≤ Aw * Bx := one_le_mul_of_one_le_of_one_le hAw hBx
    exact one_le_mul_of_one_le_of_one_le h1 hc1'
  have hD0 : 0 < D := lt_of_lt_of_le zero_lt_one hD1
  refine ⟨1 / 2 + Real.logb q D, fun s hs => ?_⟩
  set r : ℝ := (q : ℝ) ^ (-(s.re - 1 / 2)) with hr
  have hr0 : 0 < r := Real.rpow_pos_of_pos (by positivity) _
  have hDr : D * r < 1 := by
    have h1 : D < (q : ℝ) ^ (s.re - 1 / 2) := by
      have h2 : Real.logb q D < s.re - 1 / 2 := by linarith
      calc
        D = (q : ℝ) ^ (Real.logb q D) :=
          (Real.rpow_logb (by positivity) hq1'.ne' hD0).symm
        _ < (q : ℝ) ^ (s.re - 1 / 2) := Real.rpow_lt_rpow_of_exponent_lt hq1' h2
    have h3 : r = ((q : ℝ) ^ (s.re - 1 / 2))⁻¹ := Real.rpow_neg (by positivity) _
    rw [h3, ← div_eq_mul_inv, div_lt_one (by positivity)]
    exact h1
  have hnormq : ‖((q : ℂ) ^ (-(s - 1 / 2)))‖ = r := by
    rw [Complex.norm_natCast_cpow_of_pos hq0]
    congr 1
    simp only [Complex.neg_re, Complex.sub_re, Complex.one_re, Complex.div_re,
      Complex.normSq_ofNat]
    norm_num
  -- the integrand and its cellwise bound
  set f := corankOneIntegrand ψ abv w.val
    (inverseSphericalWhittaker h.conductor.1 h.uniformizer q x) s with hf
  let S : (Fin (n + 1) → ℤ) → ℕ := fun lam => ∑ i, (lam i).natAbs
  let E : (Fin (n + 1) → ℤ) → ℝ := fun lam =>
    if Antitone lam ∧ b ≤ lam (Fin.last n) then
      Cw * Aw ^ S lam * (Cx * Bx ^ S lam) * r ^ (∑ i, lam i) else 0
  have hE0 : ∀ lam, 0 ≤ E lam := by
    intro lam
    simp only [E]
    split_ifs
    · positivity
    · exact le_rfl
  have hpt : ∀ lam, ∀ t ∈ sphericalCell h.uniformizer lam, ‖f t‖ ≤ E lam := by
    intro lam t ht
    rw [sphericalCell_eq_image] at ht
    obtain ⟨k, hk, rfl⟩ := ht
    change ‖f (Quotient.mk _ (torus ϖ lam * k))‖ ≤ E lam
    rw [hf, corankOneIntegrand_torus_mul h _ _ _ _ hk]
    obtain ⟨hWb, hWa⟩ := hW lam k hk
    by_cases ha : Antitone lam
    · by_cases hbl : b ≤ lam (Fin.last n)
      · simp only [E, ite_eq_left ha, ite_eq_left (⟨ha, hbl⟩ : Antitone lam ∧ _)]
        rw [norm_mul, norm_mul, norm_zpow, hnormq]
        have h1 := hWa ha
        have h2 := hX lam
        gcongr
      · have hz : w.val.val (rankInclusion 1 (torus ϖ lam * k)) = 0 := by
          by_contra hne
          exact hbl (hWb hne)
        rw [hz, zero_mul, zero_mul, norm_zero]
        exact hE0 lam
    · simp only [ite_eq_right ha, mul_zero, zero_mul, norm_zero]
      exact hE0 lam
  have hcont := corankOneIntegrand_model_continuous h π hπ.1 w x s
  have hmeas : AEStronglyMeasurable f μ := hcont.aestronglyMeasurable
  have hint : ∀ lam, IntegrableOn f (sphericalCell h.uniformizer lam) μ := fun lam =>
    Measure.integrableOn_of_bounded (sphericalCell_measure h lam).2.ne hmeas
      (ae_restrict_of_forall_mem (isOpen_sphericalCell h.uniformizer lam).measurableSet
        (hpt lam))
  have hint_le : ∀ lam, ∫ t in sphericalCell h.uniformizer lam, ‖f t‖ ∂μ ≤
      E lam * (M0 * (c : ℝ) ^ S lam) := by
    intro lam
    have h1 := norm_setIntegral_le_of_norm_le_const (μ := μ) (f := fun t => ‖f t‖)
      (sphericalCell_measure h lam).2 (fun t ht => by rw [norm_norm]; exact hpt lam t ht)
    have h2 : μ.real (sphericalCell h.uniformizer lam) ≤ M0 * (c : ℝ) ^ S lam := by
      have h3 := hcell lam
      rw [measureReal_def]
      calc
        (μ (sphericalCell h.uniformizer lam)).toReal ≤
            (μ (sphericalCell h.uniformizer 0) * (c : ENNReal) ^ S lam).toReal :=
          ENNReal.toReal_mono (ENNReal.mul_ne_top (sphericalCell_measure h 0).2.ne
            (ENNReal.pow_ne_top (ENNReal.natCast_ne_top c))) h3
        _ = M0 * (c : ℝ) ^ S lam := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_natCast, hM0,
            measureReal_def]
    calc
      ∫ t in sphericalCell h.uniformizer lam, ‖f t‖ ∂μ ≤
          ‖∫ t in sphericalCell h.uniformizer lam, ‖f t‖ ∂μ‖ := Real.le_norm_self _
      _ ≤ E lam * μ.real (sphericalCell h.uniformizer lam) := h1
      _ ≤ E lam * (M0 * (c : ℝ) ^ S lam) := mul_le_mul_of_nonneg_left h2 (hE0 lam)
  -- summability of the bounds
  let G : ℤ → ℝ := fun z => if b ≤ z then D ^ z.natAbs * r ^ z else 0
  have hG0 : ∀ z, 0 ≤ G z := by
    intro z
    simp only [G]
    split_ifs
    · positivity
    · exact le_rfl
  have hG : Summable G := by
    refine Summable.of_nonneg_of_le hG0 (fun z => ?_)
      (summable_shifted_geometric b (mul_pos hD0 hr0) hDr (D ^ (2 * b.natAbs)))
    simp only [G]
    split_ifs with hbz
    · have hexp : ((z.natAbs : ℤ)) ≤ ((2 * b.natAbs : ℕ) : ℤ) + z := by omega
      have h1 : D ^ z.natAbs ≤ D ^ (2 * b.natAbs) * D ^ z := by
        rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hD0.ne']
        exact zpow_le_zpow_right₀ hD1 hexp
      calc
        D ^ z.natAbs * r ^ z ≤ D ^ (2 * b.natAbs) * D ^ z * r ^ z :=
          mul_le_mul_of_nonneg_right h1 (zpow_nonneg hr0.le _)
        _ = D ^ (2 * b.natAbs) * (D * r) ^ z := by rw [mul_zpow D r z]; ring
    · exact le_rfl
  have hprod := (summable_prod_fin hG hG0 n).mul_left (Cw * Cx * M0)
  have hsum : Summable (fun lam => ∫ t in sphericalCell h.uniformizer lam, ‖f t‖ ∂μ) := by
    refine Summable.of_nonneg_of_le (fun lam => integral_nonneg fun t => norm_nonneg _)
      (fun lam => le_trans (hint_le lam) ?_) hprod
    simp only [E]
    split_ifs with hcond
    · obtain ⟨ha, hbl⟩ := hcond
      have hall : ∀ i, b ≤ lam i := fun i => le_trans hbl (ha (Fin.le_last i))
      have hGi : ∀ i, G (lam i) = D ^ (lam i).natAbs * r ^ (lam i) := fun i => by
        simp only [G, ite_eq_left (hall i)]
      have hprodG : ∏ i, G (lam i) = D ^ (S lam) * r ^ (∑ i, lam i) := by
        rw [Finset.prod_congr rfl (fun i _ => hGi i), Finset.prod_mul_distrib,
          Finset.prod_pow_eq_pow_sum, prod_real_zpow_eq r hr0.ne' Finset.univ lam]
      rw [hprodG, hD, mul_pow, mul_pow]
      exact le_of_eq (by ring)
    · rw [zero_mul]
      exact mul_nonneg (by positivity) (Finset.prod_nonneg fun i _ => hG0 _)
  have hU := integrableOn_iUnion_of_summable_integral_norm hint hsum
  have huniv : (⋃ lam : Fin (n + 1) → ℤ, sphericalCell h.uniformizer lam) =
      (Set.univ : Set (LeftUnipotentQuotient n F)) :=
    Set.eq_univ_of_forall fun t => Set.mem_iUnion.mpr ⟨_, rfl⟩
  rw [huniv, integrableOn_univ] at hU
  exact hU

end Main

end Langlands.Conductor
