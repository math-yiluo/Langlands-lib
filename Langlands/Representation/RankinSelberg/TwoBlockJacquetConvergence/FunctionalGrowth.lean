import Langlands.Representation.RankinSelberg.TwoBlockJacquetConvergence.DominantGrowth
import Langlands.Representation.RankinSelberg.UnequalRankMirabolicUnitTestProof

/-!
# Uniform geometric growth of character functionals

Let `ρ` be an admissible, finitely generated representation of `GL_(n+1)(k)` over a
nonarchimedean local field, and `ℓ` a functional transforming under the upper unipotent group
by a unitary character `θ` of the form `x ↦ χ(∑ x_(i,i+1))` with `χ` nontrivial and trivial on
a small level. With `ϖ` a uniformizer, say that `g` is bounded by `e` if `ϖ^e g` and
`ϖ^e g⁻¹` have integral entries. There is one base `B ≥ 1` such that for every vector `v`
there is `C` with `|ℓ(ρ(g) v)| ≤ C B^e` whenever `g` is bounded by `e`.

The proof writes `g = u ϖ^lam k` (Iwasawa), bounds `|lam_i| ≤ e`, shows that `ℓ(ρ(ϖ^lam) w)`
vanishes unless consecutive differences of `lam` are bounded below (support), shifts `lam`
into the antitone cone and applies `exists_dominant_bound`; finite generation reduces to
finitely many level-fixed generators.
-/

noncomputable section

namespace Langlands.RankinSelberg.TwoBlockConvergence

open Matrix MeasureTheory Langlands.Conductor Langlands.GeneralLinear

universe u uV

section Valuation

variable {k : Type u} [Field k] [ValuativeRel k]

/-- Every element becomes integral after multiplication by a power of a uniformizer. -/
theorem exists_pow_mul_mem_integer {ϖ : kˣ}
    (hϖ : Iwasawa.IsUniformizingElement (ValuativeRel.valuation k) ϖ) (z : k) :
    ∃ e : ℕ, (ϖ : k) ^ e * z ∈ (ValuativeRel.valuation k).integer := by
  by_cases hz : z = 0
  · exact ⟨0, by rw [hz, mul_zero]; exact zero_mem _⟩
  obtain ⟨m, hm⟩ := hϖ.2 z hz
  have hpos := Iwasawa.valuation_pos (ValuativeRel.valuation k) ϖ
  refine ⟨(-m).toNat, ?_⟩
  rw [Valuation.mem_integer_iff, map_mul, map_pow, hm, ← zpow_natCast,
    ← zpow_add₀ hpos.ne']
  exact (zpow_le_one_iff_right_of_lt_one₀ hpos hϖ.1).mpr (by omega)

theorem pow_mul_mem_integer_of_le {ϖ : kˣ} (hϖ : ValuativeRel.valuation k (ϖ : k) ≤ 1)
    {e e' : ℕ} (hee' : e ≤ e') {z : k}
    (hz : (ϖ : k) ^ e * z ∈ (ValuativeRel.valuation k).integer) :
    (ϖ : k) ^ e' * z ∈ (ValuativeRel.valuation k).integer := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hee'
  rw [pow_add, mul_comm ((ϖ : k) ^ e), mul_assoc]
  exact mul_mem (pow_mem ((Valuation.mem_integer_iff _ _).2 hϖ) d) hz

/-- An integral power of a uniformizer has nonnegative exponent. -/
theorem nonneg_of_zpow_mem_integer {ϖ : kˣ}
    (hϖ : Iwasawa.IsUniformizingElement (ValuativeRel.valuation k) ϖ) {m : ℤ}
    (h : ((ϖ ^ m : kˣ) : k) ∈ (ValuativeRel.valuation k).integer) : 0 ≤ m := by
  have hpos := Iwasawa.valuation_pos (ValuativeRel.valuation k) ϖ
  rw [Valuation.mem_integer_iff, Units.val_zpow_eq_zpow_val, map_zpow₀] at h
  exact (zpow_le_one_iff_right_of_lt_one₀ hpos hϖ.1).mp h

theorem zpow_mem_integer_of_nonneg {ϖ : kˣ} (hϖ : ValuativeRel.valuation k (ϖ : k) ≤ 1)
    {m : ℤ} (hm : 0 ≤ m) : ((ϖ ^ m : kˣ) : k) ∈ (ValuativeRel.valuation k).integer := by
  lift m to ℕ using hm
  rw [zpow_natCast, Units.val_pow_eq_pow_val]
  exact pow_mem ((Valuation.mem_integer_iff _ _).2 hϖ) m

/-- A uniformizer lies in the maximal ideal of the valuation integers. -/
theorem uniformizer_mem_maximalIdeal {ϖ : kˣ}
    (hϖ : Iwasawa.IsUniformizingElement (ValuativeRel.valuation k) ϖ) :
    (⟨(ϖ : k), (Valuation.mem_integer_iff _ _).2 hϖ.1.le⟩ :
        (ValuativeRel.valuation k).integer) ∈
      IsLocalRing.maximalIdeal (ValuativeRel.valuation k).integer := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    (Valuation.integer.integers (ValuativeRel.valuation k)).isUnit_iff_valuation_eq_one]
  exact hϖ.1.ne

/-- A power `ϖ^a z` with `z` integral lies in the level set `𝔪^a`. -/
theorem pow_mul_mem_levelSet {ϖ : kˣ}
    (hϖ : Iwasawa.IsUniformizingElement (ValuativeRel.valuation k) ϖ) (a : ℕ) {z : k}
    (hz : z ∈ (ValuativeRel.valuation k).integer) :
    (ϖ : k) ^ a * z ∈ UnequalRankMirabolicUnitTest.levelSet k a :=
  ⟨⟨(ϖ : k), (Valuation.mem_integer_iff _ _).2 hϖ.1.le⟩ ^ a * ⟨z, hz⟩,
    Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (uniformizer_mem_maximalIdeal hϖ) a), rfl⟩

end Valuation

section Bounded

variable {k : Type u} [Field k] [ValuativeRel k]

/-- `g` is bounded by `e` when `ϖ^e g` and `ϖ^e g⁻¹` have integral entries. -/
def IsEntryBounded {m : ℕ} (ϖ : kˣ) (e : ℕ) (g : GeneralLinear m k) : Prop :=
  ∀ i j, (ϖ : k) ^ e * g i j ∈ (ValuativeRel.valuation k).integer ∧
    (ϖ : k) ^ e * (g⁻¹ : GeneralLinear m k) i j ∈ (ValuativeRel.valuation k).integer

theorem IsEntryBounded.mul {m : ℕ} {ϖ : kˣ} {e e' : ℕ} {g h : GeneralLinear m k}
    (hg : IsEntryBounded ϖ e g) (hh : IsEntryBounded ϖ e' h) :
    IsEntryBounded ϖ (e + e') (g * h) := by
  intro i j
  constructor
  · rw [Units.val_mul, Matrix.mul_apply, Finset.mul_sum]
    refine Subring.sum_mem _ fun l _ => ?_
    rw [show (ϖ : k) ^ (e + e') * ((g : Matrix (Fin m) (Fin m) k) i l * h l j) =
        ((ϖ : k) ^ e * g i l) * ((ϖ : k) ^ e' * h l j) by ring]
    exact mul_mem (hg i l).1 (hh l j).1
  · rw [_root_.mul_inv_rev, Units.val_mul, Matrix.mul_apply, Finset.mul_sum]
    refine Subring.sum_mem _ fun l _ => ?_
    rw [show (ϖ : k) ^ (e + e') * (((h⁻¹ : GeneralLinear m k) : Matrix (Fin m) (Fin m) k) i l *
        (g⁻¹ : GeneralLinear m k) l j) =
        ((ϖ : k) ^ e' * (h⁻¹ : GeneralLinear m k) i l) *
          ((ϖ : k) ^ e * (g⁻¹ : GeneralLinear m k) l j) by ring]
    exact mul_mem (hh i l).2 (hg l j).2

theorem IsEntryBounded.mono {m : ℕ} {ϖ : kˣ} (hϖ : ValuativeRel.valuation k (ϖ : k) ≤ 1)
    {e e' : ℕ} (hee' : e ≤ e') {g : GeneralLinear m k} (hg : IsEntryBounded ϖ e g) :
    IsEntryBounded ϖ e' g := fun i j =>
  ⟨pow_mul_mem_integer_of_le hϖ hee' (hg i j).1, pow_mul_mem_integer_of_le hϖ hee' (hg i j).2⟩

/-- Every invertible matrix is bounded by some exponent. -/
theorem exists_isEntryBounded {m : ℕ} {ϖ : kˣ}
    (hϖ : Iwasawa.IsUniformizingElement (ValuativeRel.valuation k) ϖ) (g : GeneralLinear m k) :
    ∃ e, IsEntryBounded ϖ e g := by
  have h : ∀ z : k, ∀ᶠ e in Filter.atTop,
      (ϖ : k) ^ e * z ∈ (ValuativeRel.valuation k).integer := fun z => by
    obtain ⟨e₀, he₀⟩ := exists_pow_mul_mem_integer hϖ z
    exact Filter.eventually_atTop.2 ⟨e₀, fun e he => pow_mul_mem_integer_of_le hϖ.1.le he he₀⟩
  have hall : ∀ᶠ e in Filter.atTop, IsEntryBounded ϖ e g := by
    simp only [IsEntryBounded, Filter.eventually_all]
    exact fun i j => (h _).and (h _)
  exact hall.exists

/-- Integral invertible matrices are bounded by `0`. -/
theorem isEntryBounded_zero_of_mem {m : ℕ} (ϖ : kˣ) {γ : GeneralLinear (m + 1) k}
    (hγ : γ ∈ integralSubgroup (ValuativeRel.valuation k).integer m) :
    IsEntryBounded ϖ 0 γ := by
  obtain ⟨h₁, h₂⟩ := (Conductor.mem_integralSubgroup _ m γ).1 hγ
  intro i j
  simp only [pow_zero, one_mul]
  exact ⟨h₁ i j, h₂ i j⟩

/-- **Iwasawa exponents of a bounded matrix.** If `u ϖ^lam γ` is bounded by `e`, with `u`
upper unipotent and `γ` integral, then `|lam_i| ≤ e`. -/
theorem abs_le_of_isEntryBounded {n : ℕ} {ϖ : kˣ}
    (hϖ : Iwasawa.IsUniformizingElement (ValuativeRel.valuation k) ϖ) {e : ℕ}
    {u : GeneralLinear (n + 1) k} (hu : u ∈ upperUnipotent (n + 1) k)
    {lam : Fin (n + 1) → ℤ} {γ : GeneralLinear (n + 1) k}
    (hγ : γ ∈ integralSubgroup (ValuativeRel.valuation k).integer n)
    (hg : IsEntryBounded ϖ e (u * Iwasawa.torus ϖ lam * γ)) (i : Fin (n + 1)) :
    -(e : ℤ) ≤ lam i ∧ lam i ≤ e := by
  have h := hg.mul (isEntryBounded_zero_of_mem ϖ (inv_mem hγ))
  rw [mul_inv_cancel_right, add_zero] at h
  obtain ⟨h₁, h₂⟩ := h i i
  have hdiag : ((u * Iwasawa.torus ϖ lam : GeneralLinear (n + 1) k) : Matrix _ _ k) i i =
      ((ϖ ^ lam i : kˣ) : k) := by
    rw [Units.val_mul, Iwasawa.torus_val, Matrix.mul_diagonal, hu.2 i, one_mul]
  have hdiag' : (((u * Iwasawa.torus ϖ lam)⁻¹ : GeneralLinear (n + 1) k) : Matrix _ _ k) i i =
      (((ϖ ^ lam i)⁻¹ : kˣ) : k) := by
    rw [_root_.mul_inv_rev, Units.val_mul, Iwasawa.torus_inv_val, Matrix.diagonal_mul,
      (inv_mem hu).2 i, mul_one]
  have hpow : ∀ m : ℤ, (ϖ : k) ^ e * ((ϖ ^ m : kˣ) : k) = ((ϖ ^ ((e : ℤ) + m) : kˣ) : k) := by
    intro m
    rw [zpow_add, zpow_natCast, Units.val_mul, Units.val_pow_eq_pow_val]
  change (ϖ : k) ^ e * ((u * Iwasawa.torus ϖ lam : GeneralLinear (n + 1) k) :
    Matrix _ _ k) i i ∈ _ at h₁
  change (ϖ : k) ^ e * (((u * Iwasawa.torus ϖ lam)⁻¹ : GeneralLinear (n + 1) k) :
    Matrix _ _ k) i i ∈ _ at h₂
  rw [hdiag, hpow] at h₁
  rw [hdiag', ← zpow_neg, hpow] at h₂
  have := nonneg_of_zpow_mem_integer hϖ h₁
  have := nonneg_of_zpow_mem_integer hϖ h₂
  constructor <;> omega

end Bounded

section Support

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
variable {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- **Support of torus values.** Let `ℓ` transform under the upper unipotent group by
`x ↦ χ(∑ x_(i,i+1))`, with `χ(x₀) ≠ 1` and `ϖ^c₀ x₀` integral. If `w` is fixed by the
positive principal level `K(a)` and `ℓ(ρ(ϖ^lam) w) ≠ 0`, then
`lam_i - lam_(i+1) > -(a + c₀)` for every `i`. -/
theorem neg_lt_sub_of_ne_zero (ρ : Representation ℂ (GeneralLinear (n + 1) k) V)
    (ℓ : V →ₗ[ℂ] ℂ) (χ : k → ℂ)
    (hℓ : ∀ x ∈ upperUnipotent (n + 1) k, ∀ v,
      ℓ (ρ x v) = χ (∑ i : Fin n, x i.castSucc i.succ) * ℓ v)
    {ϖ : kˣ} (hϖ : Iwasawa.IsUniformizingElement (ValuativeRel.valuation k) ϖ)
    {x₀ : k} (hx₀ : χ x₀ ≠ 1) {c₀ : ℕ}
    (hc₀ : (ϖ : k) ^ c₀ * x₀ ∈ (ValuativeRel.valuation k).integer)
    {a : ℕ} (ha : 0 < a) {w : V}
    (hw : w ∈ fixedVectors ρ (principalLevelOpenSubgroup k n a).toSubgroup)
    {lam : Fin (n + 1) → ℤ} (hne : ℓ (ρ (Iwasawa.torus ϖ lam) w) ≠ 0) (i : Fin n) :
    -((a : ℤ) + c₀) < lam i.castSucc - lam i.succ := by
  classical
  by_contra hle
  push Not at hle
  set d := lam i.castSucc - lam i.succ with hd
  set y : k := ((ϖ ^ (-d) : kˣ) : k) * x₀ with hy
  have hsplit : y = (ϖ : k) ^ a * (((ϖ ^ (-d - a - c₀) : kˣ) : k) * ((ϖ : k) ^ c₀ * x₀)) := by
    have hu : (ϖ ^ (-d) : kˣ) = ϖ ^ a * ϖ ^ (-d - a - c₀) * ϖ ^ c₀ := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_add, ← zpow_add]
      congr 1
      ring
    rw [hy, hu]
    push_cast
    ring
  have hyl : y ∈ UnequalRankMirabolicUnitTest.levelSet k a := by
    rw [hsplit]
    exact pow_mul_mem_levelSet hϖ a
      (mul_mem (zpow_mem_integer_of_nonneg hϖ.1.le (by omega)) hc₀)
  set Y : Matrix (Fin (n + 1)) (Fin (n + 1)) k := 1 + Matrix.single i.castSucc i.succ y with hY
  have hcs : i.castSucc ≠ i.succ := (Fin.castSucc_lt_succ (i := i)).ne
  obtain ⟨E, hE, hEY⟩ := UnequalRankMirabolicUnitTest.exists_mem_principalLevelSubgroup ha Y
    (fun p q => by
      rw [hY, Matrix.add_apply, add_sub_cancel_left]
      by_cases h : i.castSucc = p ∧ i.succ = q
      · obtain ⟨rfl, rfl⟩ := h
        rw [Matrix.single_apply_same]
        exact hyl
      · rw [Matrix.single_apply_of_ne (h := h)]
        exact UnequalRankMirabolicUnitTest.zero_mem_levelSet a)
  have hEN : E ∈ upperUnipotent (n + 1) k := by
    refine ⟨fun p q hpq => ?_, fun p => ?_⟩
    · have hpq' : q < p := hpq
      change (E : Matrix _ _ k) p q = 0
      rw [hEY, hY, Matrix.add_apply, Matrix.one_apply_ne (ne_of_gt hpq'), zero_add]
      refine Matrix.single_apply_of_ne (c := y) (h := ?_)
      rintro ⟨rfl, rfl⟩
      exact absurd hpq' (not_lt.mpr (Fin.castSucc_lt_succ (i := i)).le)
    · change (E : Matrix _ _ k) p p = 1
      rw [hEY, hY, Matrix.add_apply, Matrix.one_apply_eq, Matrix.single_apply_of_ne (h := ?_),
        add_zero]
      rintro ⟨rfl, h⟩
      exact hcs h.symm
  set t := Iwasawa.torus ϖ lam
  have hxN : t * E * t⁻¹ ∈ upperUnipotent (n + 1) k :=
    diagonalUnits_conj_mem_upperUnipotent _ hEN
  have hsum : ∑ j : Fin n, (t * E * t⁻¹ : GeneralLinear (n + 1) k) j.castSucc j.succ = x₀ := by
    have hentry : ∀ j : Fin n, (t * E * t⁻¹ : GeneralLinear (n + 1) k) j.castSucc j.succ =
        ((ϖ ^ lam j.castSucc : kˣ) : k) * (E : Matrix _ _ k) j.castSucc j.succ *
          (((ϖ ^ lam j.succ)⁻¹ : kˣ) : k) := fun j => by
      rw [show t⁻¹ = Iwasawa.diagonalUnits fun j => (ϖ ^ lam j)⁻¹ from Iwasawa.torus_inv ϖ lam]
      exact Iwasawa.diagonalUnits_mul_mul_apply _ _ E _ _
    simp_rw [hentry]
    rw [Finset.sum_eq_single i]
    · rw [hEY, hY, Matrix.add_apply, Matrix.one_apply_ne hcs, zero_add, Matrix.single_apply_same]
      have hu : ϖ ^ lam i.castSucc * ϖ ^ (-d) * (ϖ ^ lam i.succ)⁻¹ = 1 := by
        rw [← zpow_neg, ← zpow_add, ← zpow_add]
        convert zpow_zero ϖ using 2
        omega
      calc
        _ = ((ϖ ^ lam i.castSucc * ϖ ^ (-d) * (ϖ ^ lam i.succ)⁻¹ : kˣ) : k) * x₀ := by
          rw [hy]
          push_cast
          ring
        _ = x₀ := by rw [hu, Units.val_one, one_mul]
    · intro j _ hji
      rw [hEY, hY, Matrix.add_apply, Matrix.one_apply_ne (Fin.castSucc_lt_succ (i := j)).ne,
        zero_add, Matrix.single_apply_of_ne (h := ?_), mul_zero, zero_mul]
      rintro ⟨h, -⟩
      exact hji (Fin.castSucc_injective n h).symm
    · intro h
      exact absurd (Finset.mem_univ i) h
  have hEw : ρ E w = w := (Representation.mem_invariants _ w).1 hw ⟨E, hE⟩
  have hrel : ρ t w = ρ (t * E * t⁻¹) (ρ t w) := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right, map_mul, Module.End.mul_apply,
      hEw]
  have hval : ℓ (ρ t w) = χ x₀ * ℓ (ρ t w) := by
    conv_lhs => rw [hrel]
    rw [hℓ _ hxN, hsum]
  have : (χ x₀ - 1) * ℓ (ρ t w) = 0 := by
    rw [sub_mul, one_mul, ← hval, sub_self]
  exact mul_ne_zero (sub_ne_zero.2 hx₀) hne this

end Support

section Orbit

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
variable {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- A smooth vector has finitely many translates under the integral group. -/
theorem finite_integral_orbit (ρ : Representation ℂ (GeneralLinear (n + 1) k) V)
    (hρ : IsSmooth ρ) (w : V) :
    ((fun γ => ρ γ w) '' (integralSubgroup (ValuativeRel.valuation k).integer n :
      Set (GeneralLinear (n + 1) k))).Finite := by
  obtain ⟨K, hK⟩ := hρ w
  let _ : TopologicalSpace V := ⊥
  have : DiscreteTopology V := ⟨rfl⟩
  have hlc : IsLocallyConstant fun γ : GeneralLinear (n + 1) k => ρ γ w := by
    apply (IsLocallyConstant.iff_exists_open _).2
    intro γ
    refine ⟨(fun g => γ⁻¹ * g) ⁻¹' (K : Set (GeneralLinear (n + 1) k)),
      K.isOpen.preimage (continuous_const.mul continuous_id), by simp, ?_⟩
    intro g hg
    have hfix : ρ (γ⁻¹ * g) w = w := (Representation.mem_invariants _ w).1 hK ⟨_, hg⟩
    calc
      ρ g w = ρ γ (ρ (γ⁻¹ * g) w) := by
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
      _ = ρ γ w := by rw [hfix]
  have hcpt : IsCompact (integralSubgroup (ValuativeRel.valuation k).integer n :
      Set (GeneralLinear (n + 1) k)) := by
    rw [← Iwasawa.integralRange_succ]
    exact isCompact_integralRange k (n + 1)
  exact (hcpt.image hlc.continuous).finite_of_discrete

end Orbit

section Growth

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
variable {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem levelSet_anti {a b : ℕ} (hab : a ≤ b) :
    UnequalRankMirabolicUnitTest.levelSet k b ⊆ UnequalRankMirabolicUnitTest.levelSet k a := by
  rintro z ⟨y, hy, rfl⟩
  exact ⟨y, Ideal.pow_le_pow_right hab hy, rfl⟩

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/-- If `χ` is trivial on `𝔪^a₀`, the functional is invariant under `K(a) ∩ N` for `a ≥ a₀`. -/
theorem dual_eq_of_mem_principalLevel (ρ : Representation ℂ (GeneralLinear (n + 1) k) V)
    (ℓ : V →ₗ[ℂ] ℂ) (χ : k → ℂ)
    (hℓ : ∀ x ∈ upperUnipotent (n + 1) k, ∀ v,
      ℓ (ρ x v) = χ (∑ i : Fin n, x i.castSucc i.succ) * ℓ v)
    {a₀ a : ℕ} (hχ : ∀ z ∈ UnequalRankMirabolicUnitTest.levelSet k a₀, χ z = 1)
    (ha : a₀ ≤ a) :
    ∀ x ∈ principalLevelSubgroup k n a, x ∈ upperUnipotent (n + 1) k →
      ∀ v, ℓ (ρ x v) = ℓ v := by
  intro x hxP hxN v
  rw [hℓ x hxN, hχ _ ?_, one_mul]
  apply levelSet_anti ha
  apply UnequalRankMirabolicUnitTest.sum_mem_levelSet
  intro i _
  have := ((UnequalRankMirabolicUnitTest.mem_principalLevelSubgroup_iff x).1 hxP).1
    i.castSucc i.succ
  rwa [Matrix.one_apply_ne (Fin.castSucc_lt_succ (i := i)).ne, sub_zero] at this

/-- Integral translates of a `K(a)`-fixed vector are `K(a)`-fixed. -/
theorem integral_smul_mem_fixedVectors (ρ : Representation ℂ (GeneralLinear (n + 1) k) V)
    {a : ℕ} {γ : GeneralLinear (n + 1) k}
    (hγ : γ ∈ integralSubgroup (ValuativeRel.valuation k).integer n) {w : V}
    (hw : w ∈ fixedVectors ρ (principalLevelOpenSubgroup k n a).toSubgroup) :
    ρ γ w ∈ fixedVectors ρ (principalLevelOpenSubgroup k n a).toSubgroup := by
  rw [fixedVectors, Representation.mem_invariants]
  rintro ⟨x, hx⟩
  change ρ x (ρ γ w) = ρ γ w
  have hconj : γ⁻¹ * x * γ⁻¹⁻¹ ∈ principalLevelSubgroup k n a :=
    conj_mem_rankPrincipalLevel (k := k) (m := n + 1) (inv_mem hγ) hx
  rw [inv_inv] at hconj
  have hfix : ρ (γ⁻¹ * x * γ) w = w := (Representation.mem_invariants _ w).1 hw ⟨_, hconj⟩
  calc
    ρ x (ρ γ w) = ρ γ (ρ (γ⁻¹ * x * γ) w) := by
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      congr 2
      group
    _ = ρ γ w := by rw [hfix]

/-- **Growth at a fixed level.** Let `ℓ` transform under the upper unipotent group by
`x ↦ χ(∑ x_(i,i+1))`, with `χ` of absolute value one, `χ(x₀) ≠ 1` and `χ` trivial on
`𝔪^a` for some `a > 0`. For an admissible representation there is `B ≥ 1` such that every
`K(a)`-fixed vector `w` satisfies `|ℓ(ρ(g) w)| ≤ C_w B^e` whenever `g` is bounded by `e`. -/
theorem exists_growth_fixed (ρ : Representation ℂ (GeneralLinear (n + 1) k) V)
    (hρ : IsAdmissible ρ) (ℓ : V →ₗ[ℂ] ℂ) (χ : k → ℂ)
    (hℓ : ∀ x ∈ upperUnipotent (n + 1) k, ∀ v,
      ℓ (ρ x v) = χ (∑ i : Fin n, x i.castSucc i.succ) * ℓ v)
    (hχ1 : ∀ z, ‖χ z‖ = 1)
    {ϖ : kˣ} (hϖ : Iwasawa.IsUniformizingElement (ValuativeRel.valuation k) ϖ)
    {x₀ : k} (hx₀ : χ x₀ ≠ 1) {c₀ : ℕ}
    (hc₀ : (ϖ : k) ^ c₀ * x₀ ∈ (ValuativeRel.valuation k).integer)
    {a : ℕ} (ha : 0 < a) (hχ : ∀ z ∈ UnequalRankMirabolicUnitTest.levelSet k a, χ z = 1) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ w ∈ fixedVectors ρ (principalLevelOpenSubgroup k n a).toSubgroup,
      ∃ C : ℝ, ∀ (e : ℕ) (g : GeneralLinear (n + 1) k), IsEntryBounded ϖ e g →
        ‖ℓ (ρ g w)‖ ≤ C * B ^ e := by
  classical
  set r : ℕ := a + c₀ with hr
  set δ : Fin (n + 1) → ℤ := fun i => (r : ℤ) * (i.val : ℤ) with hδ
  set tδ := Iwasawa.torus ϖ δ with htδ
  obtain ⟨a₁, -, hsub⟩ := exists_pos_principalLevelOpenSubgroup_subset (k := k) n
    (U := (fun x => tδ⁻¹ * x * tδ) ⁻¹'
      (principalLevelOpenSubgroup k n a : Set (GeneralLinear (n + 1) k)))
    (IsOpen.mem_nhds ((principalLevelOpenSubgroup k n a).isOpen.preimage
      ((continuous_const.mul continuous_id).mul continuous_const))
      (by simp only [Set.mem_preimage, mul_one, inv_mul_cancel]; exact one_mem _))
  set a' := max a₁ a with ha'def
  have ha' : 0 < a' := lt_of_lt_of_le ha (le_max_right _ _)
  have hsub' : ∀ x ∈ principalLevelSubgroup k n a',
      tδ⁻¹ * x * tδ ∈ principalLevelSubgroup k n a :=
    fun x hx => hsub (principalLevelSubgroup_antitone k n (le_max_left _ _) hx)
  obtain ⟨B₀, hB₀, hdom⟩ := exists_dominant_bound ρ hρ.1 ha' (hρ.2 _) hϖ.1.le ℓ
    (dual_eq_of_mem_principalLevel ρ ℓ χ hℓ hχ (le_max_right _ _))
  choose C hC using hdom
  let F : V → ℝ := fun v =>
    if h : v ∈ fixedVectors ρ (principalLevelOpenSubgroup k n a').toSubgroup then C v h else 0
  refine ⟨B₀ ^ 3, one_le_pow₀ hB₀, fun w hw => ?_⟩
  obtain ⟨M, hM⟩ := ((finite_integral_orbit ρ hρ.1 w).image fun w' => F (ρ tδ w')).bddAbove
  refine ⟨max M 0 * B₀ ^ (2 * (r * n)), fun e g hg => ?_⟩
  obtain ⟨u, hu, lam, γ, hγ, rfl⟩ := Iwasawa.exists_iwasawa hϖ g
  have hlam := abs_le_of_isEntryBounded hϖ hu hγ hg
  have hred : ‖ℓ (ρ (u * Iwasawa.torus ϖ lam * γ) w)‖ =
      ‖ℓ (ρ (Iwasawa.torus ϖ lam) (ρ γ w))‖ := by
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hℓ u hu, norm_mul, hχ1,
      one_mul]
  rw [hred]
  have hw' := integral_smul_mem_fixedVectors ρ hγ hw
  set w' := ρ γ w
  by_cases hne : ℓ (ρ (Iwasawa.torus ϖ lam) w') = 0
  · rw [hne, norm_zero]
    positivity
  have hsupp := neg_lt_sub_of_ne_zero ρ ℓ χ hℓ hϖ hx₀ hc₀ ha hw' hne
  set μ := lam - δ with hμdef
  have hμ : Antitone μ := by
    rw [Fin.antitone_iff_succ_le]
    intro i
    have := hsupp i
    simp only [hμdef, hδ, Pi.sub_apply, Fin.val_succ, Fin.val_castSucc]
    push_cast
    nlinarith
  have hw'' : ρ tδ w' ∈ fixedVectors ρ (principalLevelOpenSubgroup k n a').toSubgroup := by
    rw [fixedVectors, Representation.mem_invariants]
    rintro ⟨x, hx⟩
    change ρ x (ρ tδ w') = ρ tδ w'
    have hfix : ρ (tδ⁻¹ * x * tδ) w' = w' :=
      (Representation.mem_invariants _ w').1 hw' ⟨_, hsub' x hx⟩
    calc
      ρ x (ρ tδ w') = ρ (x * tδ) w' := by rw [map_mul, Module.End.mul_apply]
      _ = ρ (tδ * (tδ⁻¹ * x * tδ)) w' := by
        rw [show tδ * (tδ⁻¹ * x * tδ) = x * tδ by group]
      _ = ρ tδ w' := by rw [map_mul, Module.End.mul_apply, hfix]
  have hsplit : Iwasawa.torus ϖ lam = Iwasawa.torus ϖ μ * tδ := by
    rw [htδ, ← torus_add, sub_add_cancel]
  have hb := hC _ hw'' μ hμ
  have hFM : C _ hw'' ≤ max M 0 := by
    have : F (ρ tδ w') ≤ M := hM ⟨w', ⟨γ, hγ, rfl⟩, rfl⟩
    simp only [F, hw'', ↓reduceDIte] at this
    exact this.trans (le_max_left _ _)
  have hwt : coneWeight μ ≤ 3 * e + 2 * (r * n) := by
    have h0 := hlam 0
    have hl := hlam (Fin.last n)
    have hrn : ((r * n : ℕ) : ℤ) = (r : ℤ) * (n : ℤ) := by push_cast; ring
    unfold coneWeight
    simp only [hμdef, hδ, Pi.sub_apply, Fin.val_zero, Fin.val_last, Nat.cast_zero, mul_zero,
      sub_zero]
    rw [← hrn]
    generalize r * n = N at *
    omega
  calc
    ‖ℓ (ρ (Iwasawa.torus ϖ lam) w')‖ = ‖ℓ (ρ (Iwasawa.torus ϖ μ) (ρ tδ w'))‖ := by
      rw [hsplit, map_mul, Module.End.mul_apply]
    _ ≤ C _ hw'' * B₀ ^ coneWeight μ := hb
    _ ≤ max M 0 * B₀ ^ (3 * e + 2 * (r * n)) :=
      mul_le_mul hFM (pow_le_pow_right₀ hB₀ hwt) (by positivity) (le_max_right _ _)
    _ = max M 0 * B₀ ^ (2 * (r * n)) * (B₀ ^ 3) ^ e := by ring

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/-- The vectors with geometric growth for a fixed base `B` are closed under the action of
the group algebra. -/
theorem growth_asAlgebraHom (ρ : Representation ℂ (GeneralLinear (n + 1) k) V)
    (ℓ : V →ₗ[ℂ] ℂ) {ϖ : kˣ} (hϖ : Iwasawa.IsUniformizingElement (ValuativeRel.valuation k) ϖ)
    (B : ℝ) {v : V}
    (hv : ∃ C : ℝ, ∀ (e : ℕ) (g : GeneralLinear (n + 1) k), IsEntryBounded ϖ e g →
      ‖ℓ (ρ g v)‖ ≤ C * B ^ e)
    (r : MonoidAlgebra ℂ (GeneralLinear (n + 1) k)) :
    ∃ C : ℝ, ∀ (e : ℕ) (g : GeneralLinear (n + 1) k), IsEntryBounded ϖ e g →
      ‖ℓ (ρ g (ρ.asAlgebraHom r v))‖ ≤ C * B ^ e := by
  obtain ⟨C, hC⟩ := hv
  induction r using MonoidAlgebra.induction_linear with
  | zero => exact ⟨0, fun e g _ => by simp⟩
  | add x y hx hy =>
    obtain ⟨C₁, h₁⟩ := hx
    obtain ⟨C₂, h₂⟩ := hy
    refine ⟨C₁ + C₂, fun e g hg => ?_⟩
    rw [map_add, LinearMap.add_apply, map_add, map_add, add_mul]
    exact (norm_add_le _ _).trans (add_le_add (h₁ e g hg) (h₂ e g hg))
  | single h c =>
    obtain ⟨eh, heh⟩ := exists_isEntryBounded hϖ h
    refine ⟨‖c‖ * (C * B ^ eh), fun e g hg => ?_⟩
    rw [Representation.asAlgebraHom_single, LinearMap.smul_apply, map_smul, map_smul,
      norm_smul, ← Module.End.mul_apply, ← map_mul]
    calc
      ‖c‖ * ‖ℓ (ρ (g * h) v)‖ ≤ ‖c‖ * (C * B ^ (e + eh)) :=
        mul_le_mul_of_nonneg_left (hC _ _ (hg.mul heh)) (norm_nonneg _)
      _ = ‖c‖ * (C * B ^ eh) * B ^ e := by ring

/-- **Uniform geometric growth.** For an admissible representation finitely generated over
the group algebra and `ℓ` as in `exists_growth_fixed` (with `χ` trivial on some `𝔪^a₀`),
there is one base `B ≥ 1` such that every vector `v` satisfies `|ℓ(ρ(g) v)| ≤ C_v B^e`
whenever `g` is bounded by `e`. -/
theorem exists_growth (ρ : Representation ℂ (GeneralLinear (n + 1) k) V)
    (hρ : IsAdmissible ρ)
    (hfg : Module.Finite (MonoidAlgebra ℂ (GeneralLinear (n + 1) k)) ρ.asModule)
    (ℓ : V →ₗ[ℂ] ℂ) (χ : k → ℂ)
    (hℓ : ∀ x ∈ upperUnipotent (n + 1) k, ∀ v,
      ℓ (ρ x v) = χ (∑ i : Fin n, x i.castSucc i.succ) * ℓ v)
    (hχ1 : ∀ z, ‖χ z‖ = 1)
    {ϖ : kˣ} (hϖ : Iwasawa.IsUniformizingElement (ValuativeRel.valuation k) ϖ)
    {x₀ : k} (hx₀ : χ x₀ ≠ 1) {c₀ : ℕ}
    (hc₀ : (ϖ : k) ^ c₀ * x₀ ∈ (ValuativeRel.valuation k).integer)
    {a₀ : ℕ} (hχ : ∀ z ∈ UnequalRankMirabolicUnitTest.levelSet k a₀, χ z = 1) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ v : V, ∃ C : ℝ, ∀ (e : ℕ) (g : GeneralLinear (n + 1) k),
      IsEntryBounded ϖ e g → ‖ℓ (ρ g v)‖ ≤ C * B ^ e := by
  classical
  obtain ⟨m, v, hv⟩ :=
    Module.Finite.exists_fin (R := MonoidAlgebra ℂ (GeneralLinear (n + 1) k)) (M := ρ.asModule)
  have hlev : ∀ i, ∃ b : ℕ, ρ.asModuleEquiv (v i) ∈
      fixedVectors ρ (principalLevelOpenSubgroup k n b).toSubgroup := by
    intro i
    obtain ⟨K, hK⟩ := hρ.1 (ρ.asModuleEquiv (v i))
    obtain ⟨b, -, hbK⟩ := exists_pos_principalLevelOpenSubgroup_subset (k := k) n
      (K.isOpen.mem_nhds K.one_mem)
    refine ⟨b, ?_⟩
    rw [fixedVectors, Representation.mem_invariants]
    rintro ⟨x, hx⟩
    exact (Representation.mem_invariants _ _).1 hK ⟨x, hbK hx⟩
  choose b hbv using hlev
  set a := max (max a₀ 1) (Finset.univ.sup b) with hadef
  have ha : 0 < a := lt_of_lt_of_le one_pos ((le_max_right _ _).trans (le_max_left _ _))
  have hgen : ∀ i, ρ.asModuleEquiv (v i) ∈
      fixedVectors ρ (principalLevelOpenSubgroup k n a).toSubgroup := fun i => by
    rw [fixedVectors, Representation.mem_invariants]
    rintro ⟨x, hx⟩
    exact (Representation.mem_invariants _ _).1 (hbv i)
      ⟨x, principalLevelSubgroup_antitone k n
        ((Finset.le_sup (Finset.mem_univ i)).trans (le_max_right _ _)) hx⟩
  obtain ⟨B, hB, hgrowth⟩ := exists_growth_fixed ρ hρ ℓ χ hℓ hχ1 hϖ hx₀ hc₀ ha
    fun z hz => hχ z (levelSet_anti ((le_max_left _ _).trans (le_max_left _ _)) hz)
  refine ⟨B, hB, fun w => ?_⟩
  have hw : ρ.asModuleEquiv.symm w ∈ Submodule.span (MonoidAlgebra ℂ (GeneralLinear (n + 1) k))
      (Set.range v) := by
    rw [hv]
    exact Submodule.mem_top
  rw [← ρ.asModuleEquiv.apply_symm_apply w]
  generalize ρ.asModuleEquiv.symm w = m at hw ⊢
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact hgrowth _ (hgen i)
  | zero => exact ⟨0, fun e g _ => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨C₁, h₁⟩ := hx
    obtain ⟨C₂, h₂⟩ := hy
    refine ⟨C₁ + C₂, fun e g hg => ?_⟩
    rw [map_add, map_add, map_add, add_mul]
    exact (norm_add_le _ _).trans (add_le_add (h₁ e g hg) (h₂ e g hg))
  | smul r x _ hx =>
    rw [Representation.asModuleEquiv_map_smul]
    exact growth_asAlgebraHom ρ ℓ hϖ B hx r

end Growth

end Langlands.RankinSelberg.TwoBlockConvergence
