import Langlands.BushnellKutzko.LevelAttainingStratum
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter

/-! # Every level value carries a stratum

Let `ψ` be an additive character of a nonarchimedean local field `F`, trivial on `𝔭_F` but not on
`𝔬_F`.

* `exists_eq_addChar_mul`: every additive character of `𝔬_F / 𝔭_F` is `s ↦ ψ(c s)`.
* `LatticeChain.exists_mem_endFiltration_forall_eq`: for a lattice chain `𝓛` in `F^ι` and
  `m ∈ ℤ`, every character of `𝔓^m(𝓛) / 𝔓^{m+1}(𝓛)` is `x ↦ ψ(tr(b x))` for some
  `b ∈ 𝔓^{-m}(𝓛)` (Bushnell–Kutzko 1993, (1.1.6), printed p. 22, case `r = n - 1`).
* `exists_containsStratum_of_hasFixedVector`: if a class `a` of irreducible admissible
  representations of `GL_n(K)` has a nonzero vector fixed by `U^{m+1}(𝔄(𝓛))` with `m ≥ 1`, then
  `a` contains a stratum `[𝔄(𝓛), m, m - 1, b]`.
-/

noncomputable section

open ValuativeRel

namespace Langlands.BushnellKutzko

universe u uK uV

/-! ### Characters of the residue field -/

section Residue

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- A function on `𝔬_F` that turns sums into products and is trivial on `𝔭_F` is constant on
the cosets of `𝔭_F`. -/
theorem eq_of_sub_mem_maximalIdeal {φ : 𝒪[F] → ℂ} (hadd : ∀ s t, φ (s + t) = φ s * φ t)
    (h1 : ∀ s ∈ 𝓂[F], φ s = 1) {s t : 𝒪[F]} (h : s - t ∈ 𝓂[F]) : φ s = φ t := by
  have h2 := hadd t (s - t)
  rw [add_sub_cancel, h1 _ h, mul_one] at h2
  exact h2

theorem residue_surjInv_sub_mem (s : 𝒪[F]) :
    Function.surjInv IsLocalRing.residue_surjective (IsLocalRing.residue 𝒪[F] s) - s ∈ 𝓂[F] := by
  rw [← IsLocalRing.residue_eq_zero_iff, map_sub,
    Function.surjInv_eq IsLocalRing.residue_surjective, sub_self]

/-- The character of the residue field `𝓀_F` defined by a function on `𝔬_F` that turns sums
into products and is trivial on `𝔭_F`. -/
def residueAddChar (φ : 𝒪[F] → ℂ) (hadd : ∀ s t, φ (s + t) = φ s * φ t)
    (h1 : ∀ s ∈ 𝓂[F], φ s = 1) : AddChar 𝓀[F] ℂ where
  toFun x := φ (Function.surjInv IsLocalRing.residue_surjective x)
  map_zero_eq_one' := h1 _ ((IsLocalRing.residue_eq_zero_iff _).1 (Function.surjInv_eq _ _))
  map_add_eq_mul' x y := by
    rw [← hadd]
    apply eq_of_sub_mem_maximalIdeal hadd h1
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_add]
    simp [Function.surjInv_eq]

theorem residueAddChar_residue (φ : 𝒪[F] → ℂ) (hadd : ∀ s t, φ (s + t) = φ s * φ t)
    (h1 : ∀ s ∈ 𝓂[F], φ s = 1) (s : 𝒪[F]) :
    residueAddChar φ hadd h1 (IsLocalRing.residue 𝒪[F] s) = φ s :=
  eq_of_sub_mem_maximalIdeal hadd h1 (residue_surjInv_sub_mem s)

/-- **Characters of the residue field.** Let `ψ` be an additive character of `F` that is
trivial on `𝔭_F` but not on `𝔬_F`. Every function `φ` on `𝔬_F` that turns sums into products
and is trivial on `𝔭_F` has the form `s ↦ ψ(c s)` for some `c ∈ 𝔬_F`. -/
theorem exists_eq_addChar_mul (ψ : AddChar F ℂ) (hψ : ∀ a ∈ 𝓂[F], ψ (a : F) = 1)
    (hψ' : ∃ a : 𝒪[F], ψ (a : F) ≠ 1) (φ : 𝒪[F] → ℂ) (hadd : ∀ s t, φ (s + t) = φ s * φ t)
    (h1 : ∀ s ∈ 𝓂[F], φ s = 1) : ∃ c : 𝒪[F], ∀ s : 𝒪[F], φ s = ψ ((c : F) * (s : F)) := by
  classical
  have : Fintype 𝓀[F] := Fintype.ofFinite _
  have hadd' : ∀ s t : 𝒪[F], ψ ((s + t : 𝒪[F]) : F) = ψ (s : F) * ψ (t : F) := by
    intro s t
    rw [Subring.coe_add, AddChar.map_add_eq_mul]
  set ψ₀ := residueAddChar (fun s : 𝒪[F] => ψ (s : F)) hadd' hψ with hψ₀
  set φ₀ := residueAddChar φ hadd h1 with hφ₀
  have hne : ψ₀ ≠ 1 := by
    obtain ⟨a, ha⟩ := hψ'
    intro h
    apply ha
    have h2 := congrArg (fun χ : AddChar 𝓀[F] ℂ => χ (IsLocalRing.residue 𝒪[F] a)) h
    simpa [hψ₀, residueAddChar_residue] using h2
  have hinj := AddChar.to_mulShift_inj_of_isPrimitive (AddChar.IsPrimitive.of_ne_one hne)
  have hbij : Function.Bijective ψ₀.mulShift := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨hinj, AddChar.card_eq.symm⟩
  obtain ⟨c₀, hc₀⟩ := hbij.2 φ₀
  obtain ⟨c, rfl⟩ := IsLocalRing.residue_surjective c₀
  refine ⟨c, fun s => ?_⟩
  have h2 := congrArg (fun χ : AddChar 𝓀[F] ℂ => χ (IsLocalRing.residue 𝒪[F] s)) hc₀
  simp only [AddChar.mulShift_apply, ← map_mul, hψ₀, hφ₀, residueAddChar_residue] at h2
  rw [← h2, Subring.coe_mul]

end Residue

/-! ### Coordinates of the filtration in a splitting basis -/

/-- `coordShift e N = ⌈N / e⌉` for `e > 0`. -/
def coordShift (e N : ℤ) : ℤ :=
  -((-N) / e)

theorem le_mul_coordShift {e : ℤ} (he : 0 < e) (N : ℤ) : N ≤ e * coordShift e N := by
  have h1 := Int.emod_add_mul_ediv (-N) e
  have h2 := Int.emod_nonneg (-N) he.ne'
  unfold coordShift
  linarith

theorem mul_coordShift_lt {e : ℤ} (he : 0 < e) (N : ℤ) : e * coordShift e N < N + e := by
  have h1 := Int.emod_add_mul_ediv (-N) e
  have h3 := Int.emod_lt_of_pos (-N) he
  unfold coordShift
  linarith

section Coordinates

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ)
variable {ι : Type*} [Fintype ι] {κ : Type*} [Fintype κ]

include hϖ in
/-- A nonzero element of `𝔭_F` has positive valuation. -/
theorem one_le_ordOf_of_mem_maximalIdeal {s : 𝒪[F]} (hs : s ∈ 𝓂[F]) (hs0 : (s : F) ≠ 0) :
    1 ≤ ordOf hϖ (s : F) := by
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hs
  obtain ⟨t, rfl⟩ := hs
  have ht0 : (t : F) ≠ 0 := by
    intro h
    apply hs0
    rw [Subring.coe_mul, h, mul_zero]
  rw [Subring.coe_mul, ordOf_mul hϖ (coe_uniformizer_ne_zero hϖ) ht0, ordOf_uniformizer hϖ]
  have := ordOf_nonneg hϖ ht0 t.2
  omega

namespace LatticeChain

variable (𝓛 : LatticeChain 𝒪[F] F (ι → F)) (β : Module.Basis κ F (ι → F))

/-- The exponent `c_{kl}(m) = ⌈(m + ν(β_l) - ν(β_k)) / e⌉`: the least `c` with
`E_{kl}(ϖ^c) ∈ 𝔓^m(𝓛)`, for a basis `β` splitting `𝓛`. -/
def coordExp (m : ℤ) (k l : κ) : ℤ :=
  coordShift 𝓛.period (m + 𝓛.index hϖ (β l) - 𝓛.index hϖ (β k))

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Fintype ι] in
theorem period_pos' : (0 : ℤ) < 𝓛.period := by exact_mod_cast 𝓛.period_pos

omit [Fintype ι] [Fintype κ] in
theorem le_mul_coordExp (m : ℤ) (k l : κ) :
    m + 𝓛.index hϖ (β l) - 𝓛.index hϖ (β k) ≤ 𝓛.period * 𝓛.coordExp hϖ β m k l :=
  le_mul_coordShift 𝓛.period_pos' _

omit [Fintype ι] [Fintype κ] in
theorem mul_coordExp_lt (m : ℤ) (k l : κ) :
    𝓛.period * 𝓛.coordExp hϖ β m k l < m + 𝓛.index hϖ (β l) - 𝓛.index hϖ (β k) + 𝓛.period :=
  mul_coordShift_lt 𝓛.period_pos' _

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Fintype ι]
  [Fintype κ] in
theorem elementaryEnd_add (k l : κ) (s t : F) :
    elementaryEnd β k l (s + t) = elementaryEnd β k l s + elementaryEnd β k l t := by
  simp [elementaryEnd, add_smul]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Fintype ι]
  [Fintype κ] in
theorem elementaryEnd_sub (k l : κ) (s t : F) :
    elementaryEnd β k l (s - t) = elementaryEnd β k l s - elementaryEnd β k l t := by
  unfold elementaryEnd
  exact sub_smul s t ((β.coord l).smulRight (β k))

variable {𝓛 β}

omit [Fintype ι] in
/-- `E_{kl}(ϖ^{c_{kl}(m)} s) ∈ 𝔓^m(𝓛)` for `s ∈ 𝔬_F`. -/
theorem elementaryEnd_coordExp_mem (hβ : 𝓛.Splits β) (m : ℤ) (k l : κ) (s : 𝒪[F]) :
    elementaryEnd β k l ((ϖ : F) ^ 𝓛.coordExp hϖ β m k l * s) ∈ 𝓛.endFiltration m := by
  by_cases hs : (s : F) = 0
  · rw [hs, mul_zero, elementaryEnd_zero]
    exact zero_mem _
  have hϖ0 := zpow_ne_zero (𝓛.coordExp hϖ β m k l) (coe_uniformizer_ne_zero hϖ)
  rw [𝓛.elementaryEnd_mem_iff hϖ hβ k l (mul_ne_zero hϖ0 hs), ordOf_mul hϖ hϖ0 hs,
    ordOf_zpow]
  have h1 := ordOf_nonneg hϖ hs s.2
  have h2 := 𝓛.le_mul_coordExp hϖ β m k l
  have h3 := 𝓛.period_pos'
  nlinarith

omit [Fintype ι] in
/-- `E_{kl}(ϖ^{c_{kl}(m)} s) ∈ 𝔓^{m+1}(𝓛)` for `s ∈ 𝔭_F`. -/
theorem elementaryEnd_coordExp_mem_succ (hβ : 𝓛.Splits β) (m : ℤ) (k l : κ) {s : 𝒪[F]}
    (hs : s ∈ 𝓂[F]) :
    elementaryEnd β k l ((ϖ : F) ^ 𝓛.coordExp hϖ β m k l * s) ∈ 𝓛.endFiltration (m + 1) := by
  by_cases hs0 : (s : F) = 0
  · rw [hs0, mul_zero, elementaryEnd_zero]
    exact zero_mem _
  have hϖ0 := zpow_ne_zero (𝓛.coordExp hϖ β m k l) (coe_uniformizer_ne_zero hϖ)
  rw [𝓛.elementaryEnd_mem_iff hϖ hβ k l (mul_ne_zero hϖ0 hs0), ordOf_mul hϖ hϖ0 hs0,
    ordOf_zpow]
  have h1 := one_le_ordOf_of_mem_maximalIdeal hϖ hs hs0
  have h2 := 𝓛.le_mul_coordExp hϖ β m k l
  have h3 := 𝓛.period_pos'
  nlinarith

omit [Fintype ι] in
/-- If `e c_{kl}(m) ≠ m + ν(β_l) - ν(β_k)`, then `E_{kl}(ϖ^{c_{kl}(m)} s) ∈ 𝔓^{m+1}(𝓛)` for
every `s ∈ 𝔬_F`. -/
theorem elementaryEnd_coordExp_mem_succ_of_ne (hβ : 𝓛.Splits β) (m : ℤ) (k l : κ)
    (hne : 𝓛.period * 𝓛.coordExp hϖ β m k l ≠ m + 𝓛.index hϖ (β l) - 𝓛.index hϖ (β k))
    (s : 𝒪[F]) :
    elementaryEnd β k l ((ϖ : F) ^ 𝓛.coordExp hϖ β m k l * s) ∈ 𝓛.endFiltration (m + 1) := by
  by_cases hs : (s : F) = 0
  · rw [hs, mul_zero, elementaryEnd_zero]
    exact zero_mem _
  have hϖ0 := zpow_ne_zero (𝓛.coordExp hϖ β m k l) (coe_uniformizer_ne_zero hϖ)
  rw [𝓛.elementaryEnd_mem_iff hϖ hβ k l (mul_ne_zero hϖ0 hs), ordOf_mul hϖ hϖ0 hs,
    ordOf_zpow]
  have h1 := ordOf_nonneg hϖ hs s.2
  have h2 := 𝓛.le_mul_coordExp hϖ β m k l
  have h2' : m + 𝓛.index hϖ (β l) - 𝓛.index hϖ (β k) < 𝓛.period * 𝓛.coordExp hϖ β m k l :=
    lt_of_le_of_ne h2 (Ne.symm hne)
  have h3 := 𝓛.period_pos'
  nlinarith

omit [Fintype ι] in
/-- The entries of an element of `𝔓^m(𝓛)`: `x_{kl} = ϖ^{c_{kl}(m)} s` with `s ∈ 𝔬_F`. -/
theorem exists_entry_eq_coordExp (hβ : 𝓛.Splits β) {m : ℤ} {x : Module.End F (ι → F)}
    (hx : x ∈ 𝓛.endFiltration m) (k l : κ) :
    ∃ s : 𝒪[F], entry β x k l = (ϖ : F) ^ 𝓛.coordExp hϖ β m k l * s := by
  by_cases h0 : entry β x k l = 0
  · exact ⟨0, by rw [h0, Subring.coe_zero, mul_zero]⟩
  have hϖ0 := coe_uniformizer_ne_zero hϖ
  have h := 𝓛.le_of_mem_endFiltration hϖ hβ hx k l h0
  have h2 := 𝓛.mul_coordExp_lt hϖ β m k l
  have h3 := 𝓛.period_pos'
  have hlt : 𝓛.period * (𝓛.coordExp hϖ β m k l - 1) < 𝓛.period * ordOf hϖ (entry β x k l) := by
    nlinarith
  have hord := lt_of_mul_lt_mul_left hlt h3.le
  have hne : (ϖ : F) ^ (-𝓛.coordExp hϖ β m k l) * entry β x k l ≠ 0 :=
    mul_ne_zero (zpow_ne_zero _ hϖ0) h0
  have hmem : (ϖ : F) ^ (-𝓛.coordExp hϖ β m k l) * entry β x k l ∈ 𝒪[F] := by
    refine mem_integer_of_ordOf_nonneg hϖ hne ?_
    rw [ordOf_mul hϖ (zpow_ne_zero _ hϖ0) h0, ordOf_zpow]
    omega
  refine ⟨⟨_, hmem⟩, ?_⟩
  change _ = _ * ((ϖ : F) ^ (-𝓛.coordExp hϖ β m k l) * entry β x k l)
  rw [← mul_assoc, ← zpow_add₀ hϖ0, add_neg_cancel, zpow_zero, one_mul]

end LatticeChain

end Coordinates

/-! ### Products over finite sums -/

theorem fun_sum_eq_prod {A : Type*} [AddCommMonoid A] {κ : Type*} (P : AddSubmonoid A)
    (θ : A → ℂ) (h0 : θ 0 = 1) (hadd : ∀ x ∈ P, ∀ y ∈ P, θ (x + y) = θ x * θ y)
    (s : Finset κ) (f : κ → A) (hf : ∀ k ∈ s, f k ∈ P) :
    θ (∑ k ∈ s, f k) = ∏ k ∈ s, θ (f k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h0
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha,
      hadd _ (hf a (Finset.mem_insert_self a s)) _
        (sum_mem fun k hk => hf k (Finset.mem_insert_of_mem hk)),
      ih fun k hk => hf k (Finset.mem_insert_of_mem hk)]

theorem addChar_sum_eq_prod {A : Type*} [AddCommMonoid A] {κ : Type*} (ψ : AddChar A ℂ)
    (s : Finset κ) (f : κ → A) : ψ (∑ k ∈ s, f k) = ∏ k ∈ s, ψ (f k) :=
  fun_sum_eq_prod ⊤ ψ ψ.map_zero_eq_one (fun x _ y _ => ψ.map_add_eq_mul x y) s f
    (fun _ _ => AddSubmonoid.mem_top _)

/-! ### Characters of `𝔓^m / 𝔓^{m+1}` -/

section MatrixDuality

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable {ι : Type*} [Fintype ι]

namespace LatticeChain

/-- **Characters of `𝔓^m / 𝔓^{m+1}`** (BK93 (1.1.6), printed p. 22, for `r = n - 1`, over
`V = F^ι`). Let `ψ` be trivial on `𝔭_F` but not on `𝔬_F`. If `θ` turns sums of elements of
`𝔓^m(𝓛)` into products and is trivial on `𝔓^{m+1}(𝓛)`, then there is `b ∈ 𝔓^{-m}(𝓛)` with
`θ(x) = ψ(tr(b x))` for all `x ∈ 𝔓^m(𝓛)`. -/
theorem exists_mem_endFiltration_forall_eq (𝓛 : LatticeChain 𝒪[F] F (ι → F))
    (ψ : AddChar F ℂ) (hψ : ∀ a ∈ 𝓂[F], ψ (a : F) = 1) (hψ' : ∃ a : 𝒪[F], ψ (a : F) ≠ 1)
    (m : ℤ) (θ : Module.End F (ι → F) → ℂ)
    (hadd : ∀ x ∈ 𝓛.endFiltration m, ∀ y ∈ 𝓛.endFiltration m, θ (x + y) = θ x * θ y)
    (h1 : ∀ x ∈ 𝓛.endFiltration (m + 1), θ x = 1) :
    ∃ b ∈ 𝓛.endFiltration (-m), ∀ x ∈ 𝓛.endFiltration m,
      θ x = ψ (LinearMap.trace F (ι → F) (b * x)) := by
  classical
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  obtain ⟨r, β, hβ, -⟩ := exists_basis_splits_both hϖ 𝓛 𝓛
  have hϖ0 := coe_uniformizer_ne_zero hϖ
  set c := 𝓛.coordExp hϖ β m with hc
  -- the one-dimensional characters `s ↦ θ(E_{kl}(ϖ^c s))`
  have h1dim : ∀ k l, ∃ a : 𝒪[F], ∀ s : 𝒪[F],
      θ (elementaryEnd β k l ((ϖ : F) ^ c k l * s)) = ψ ((a : F) * s) := by
    intro k l
    apply exists_eq_addChar_mul ψ hψ hψ'
    · intro s t
      rw [Subring.coe_add, mul_add, elementaryEnd_add]
      exact hadd _ (elementaryEnd_coordExp_mem hϖ hβ m k l s) _
        (elementaryEnd_coordExp_mem hϖ hβ m k l t)
    · intro s hs
      exact h1 _ (elementaryEnd_coordExp_mem_succ hϖ hβ m k l hs)
  choose a ha using h1dim
  -- the matrix of `b`
  let B : Matrix (Fin r) (Fin r) F := fun l k =>
    if 𝓛.period * c k l = m + 𝓛.index hϖ (β l) - 𝓛.index hϖ (β k) then
      (a k l : F) * (ϖ : F) ^ (-c k l) else 0
  let b := Matrix.toLin β β B
  have hentry : ∀ l k, entry β b l k = B l k := by
    intro l k
    change β.repr (Matrix.toLin β β B (β k)) l = B l k
    rw [← LinearMap.toMatrix_apply, LinearMap.toMatrix_toLin]
  refine ⟨b, ?_, ?_⟩
  · rw [← sum_elementaryEnd_entry β b]
    refine Submodule.sum_mem _ fun l _ => Submodule.sum_mem _ fun k _ => ?_
    rw [hentry]
    by_cases hB : B l k = 0
    · rw [hB, elementaryEnd_zero]
      exact zero_mem _
    have hcond : 𝓛.period * c k l = m + 𝓛.index hϖ (β l) - 𝓛.index hϖ (β k) := by
      by_contra hcon
      exact hB (ite_eq_right hcon)
    have hBeq : B l k = (a k l : F) * (ϖ : F) ^ (-c k l) := ite_eq_left hcond
    have ha0 : (a k l : F) ≠ 0 := by
      intro h0
      apply hB
      rw [hBeq, h0, zero_mul]
    rw [𝓛.elementaryEnd_mem_iff hϖ hβ l k hB, hBeq,
      ordOf_mul hϖ ha0 (zpow_ne_zero _ hϖ0), ordOf_zpow]
    have h2 := ordOf_nonneg hϖ ha0 (a k l).2
    have h3 := 𝓛.period_pos'
    nlinarith
  · intro x hx
    have hxkl := fun k l => exists_entry_eq_coordExp hϖ hβ hx k l
    choose s hs using hxkl
    have hsum : ∑ k, ∑ l, elementaryEnd β k l ((ϖ : F) ^ c k l * s k l) = x := by
      conv_rhs => rw [← sum_elementaryEnd_entry β x]
      simp only [hs, hc]
    have hmem : ∀ k l, elementaryEnd β k l ((ϖ : F) ^ c k l * s k l) ∈ 𝓛.endFiltration m :=
      fun k l => elementaryEnd_coordExp_mem hϖ hβ m k l (s k l)
    have hθ0 : θ 0 = 1 := h1 0 (zero_mem _)
    rw [← hsum]
    rw [fun_sum_eq_prod (𝓛.endFiltration m).toAddSubmonoid θ hθ0 hadd _ _
      fun k _ => sum_mem fun l _ => hmem k l]
    simp_rw [fun_sum_eq_prod (𝓛.endFiltration m).toAddSubmonoid θ hθ0 hadd _ _
      fun l _ => hmem _ l]
    rw [Finset.mul_sum, map_sum, addChar_sum_eq_prod]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Finset.mul_sum, map_sum, addChar_sum_eq_prod]
    refine Finset.prod_congr rfl fun l _ => ?_
    rw [trace_mul_elementaryEnd, hentry]
    by_cases hcond : 𝓛.period * c k l = m + 𝓛.index hϖ (β l) - 𝓛.index hϖ (β k)
    · have hBeq : B l k = (a k l : F) * (ϖ : F) ^ (-c k l) := ite_eq_left hcond
      rw [hBeq, ha]
      congr 1
      rw [zpow_neg]
      field_simp
    · have hB0 : B l k = 0 := ite_eq_right hcond
      rw [hB0, mul_zero, AddChar.map_zero_eq_one]
      exact h1 _ (elementaryEnd_coordExp_mem_succ_of_ne hϖ hβ m k l hcond (s k l))

end LatticeChain

end MatrixDuality

/-! ### Residue coordinates of `𝔓^m / 𝔓^{m+1}` -/

section ResidueCoordinates

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ)
variable {ι : Type*} {κ : Type*} [Fintype κ]

/-- A fixed lift `𝓀_F → 𝔬_F` of the residue map. -/
def residueLift (a : 𝓀[F]) : 𝒪[F] :=
  Function.surjInv IsLocalRing.residue_surjective a

theorem residue_residueLift (a : 𝓀[F]) : IsLocalRing.residue 𝒪[F] (residueLift a) = a :=
  Function.surjInv_eq IsLocalRing.residue_surjective a

theorem residueLift_add_sub_mem (a b : 𝓀[F]) :
    residueLift a + residueLift b - residueLift (a + b) ∈ 𝓂[F] := by
  rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_add, residue_residueLift,
    residue_residueLift, residue_residueLift, sub_self]

theorem residueLift_zero_mem : residueLift (0 : 𝓀[F]) ∈ 𝓂[F] := by
  rw [← IsLocalRing.residue_eq_zero_iff, residue_residueLift]

theorem sub_residueLift_residue_mem (s : 𝒪[F]) :
    s - residueLift (IsLocalRing.residue 𝒪[F] s) ∈ 𝓂[F] := by
  rw [← IsLocalRing.residue_eq_zero_iff, map_sub, residue_residueLift, sub_self]

namespace LatticeChain

variable (𝓛 : LatticeChain 𝒪[F] F (ι → F)) (β : Module.Basis κ F (ι → F))

/-- The element `∑_{k,l} E_{kl}(ϖ^{c_{kl}(m)} z̃_{kl})` of `𝔓^m(𝓛)` with residue coordinates
`z : κ → κ → 𝓀_F`, where `z̃_{kl}` is the fixed lift of `z_{kl}`. -/
def coordEnd (m : ℤ) (z : κ → κ → 𝓀[F]) : Module.End F (ι → F) :=
  ∑ k, ∑ l, elementaryEnd β k l ((ϖ : F) ^ 𝓛.coordExp hϖ β m k l * (residueLift (z k l) : F))

variable {𝓛 β}

theorem coordEnd_mem (hβ : 𝓛.Splits β) (m : ℤ) (z : κ → κ → 𝓀[F]) :
    𝓛.coordEnd hϖ β m z ∈ 𝓛.endFiltration m :=
  Submodule.sum_mem _ fun k _ => Submodule.sum_mem _ fun l _ =>
    elementaryEnd_coordExp_mem hϖ hβ m k l _

theorem coordEnd_add_sub_mem (hβ : 𝓛.Splits β) (m : ℤ) (y z : κ → κ → 𝓀[F]) :
    𝓛.coordEnd hϖ β m y + 𝓛.coordEnd hϖ β m z - 𝓛.coordEnd hϖ β m (y + z) ∈
      𝓛.endFiltration (m + 1) := by
  have h : 𝓛.coordEnd hϖ β m y + 𝓛.coordEnd hϖ β m z - 𝓛.coordEnd hϖ β m (y + z) =
      ∑ k, ∑ l, elementaryEnd β k l ((ϖ : F) ^ 𝓛.coordExp hϖ β m k l *
        ((residueLift (y k l) + residueLift (z k l) - residueLift (y k l + z k l) : 𝒪[F]) :
          F)) := by
    simp only [coordEnd, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, Pi.add_apply]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [← elementaryEnd_add, ← elementaryEnd_sub]
    congr 1
    push_cast
    ring
  rw [h]
  exact Submodule.sum_mem _ fun k _ => Submodule.sum_mem _ fun l _ =>
    elementaryEnd_coordExp_mem_succ hϖ hβ m k l (residueLift_add_sub_mem _ _)

theorem coordEnd_zero_mem (hβ : 𝓛.Splits β) (m : ℤ) :
    𝓛.coordEnd hϖ β m 0 ∈ 𝓛.endFiltration (m + 1) :=
  Submodule.sum_mem _ fun k _ => Submodule.sum_mem _ fun l _ =>
    elementaryEnd_coordExp_mem_succ hϖ hβ m k l residueLift_zero_mem

/-- Every element of `𝔓^m(𝓛)` is congruent modulo `𝔓^{m+1}(𝓛)` to some `coordEnd z`. -/
theorem exists_sub_coordEnd_mem (hβ : 𝓛.Splits β) {m : ℤ} {x : Module.End F (ι → F)}
    (hx : x ∈ 𝓛.endFiltration m) :
    ∃ z : κ → κ → 𝓀[F], x - 𝓛.coordEnd hϖ β m z ∈ 𝓛.endFiltration (m + 1) := by
  have hxkl := fun k l => exists_entry_eq_coordExp hϖ hβ hx k l
  choose s hs using hxkl
  refine ⟨fun k l => IsLocalRing.residue 𝒪[F] (s k l), ?_⟩
  have h : x - 𝓛.coordEnd hϖ β m (fun k l => IsLocalRing.residue 𝒪[F] (s k l)) =
      ∑ k, ∑ l, elementaryEnd β k l ((ϖ : F) ^ 𝓛.coordExp hϖ β m k l *
        ((s k l - residueLift (IsLocalRing.residue 𝒪[F] (s k l)) : 𝒪[F]) : F)) := by
    conv_lhs => rw [← sum_elementaryEnd_entry β x]
    simp only [coordEnd, ← Finset.sum_sub_distrib, hs]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [← elementaryEnd_sub]
    congr 1
    push_cast
    ring
  rw [h]
  exact Submodule.sum_mem _ fun k _ => Submodule.sum_mem _ fun l _ =>
    elementaryEnd_coordExp_mem_succ hϖ hβ m k l (sub_residueLift_residue_mem _)

end LatticeChain

end ResidueCoordinates

/-! ### Two facts about the unit filtration -/

section Units

variable {F : Type u} [Field F] [ValuativeRel F] {V : Type*} [AddCommGroup V] [Module F V]

namespace LatticeChain

variable (𝓛 : LatticeChain 𝒪[F] F V)

/-- `U^j(𝔄)` is normalized by `U^0(𝔄) = 𝔄^×`. -/
theorem inv_mul_mul_mem_unitFiltration {g h : (Module.End F V)ˣ}
    (hg : g ∈ 𝓛.unitFiltration 0) {j : ℕ} (hh : h ∈ 𝓛.unitFiltration j) :
    g⁻¹ * h * g ∈ 𝓛.unitFiltration j := by
  obtain ⟨hg1, hg2, -⟩ := hg
  obtain ⟨hh1, hh2, hh3⟩ := hh
  refine ⟨?_, ?_, ?_⟩
  · simp only [Units.val_mul]
    exact mul_mem (mul_mem hg2 hh1) hg1
  · simp only [mul_inv_rev, inv_inv, Units.val_mul]
    exact mul_mem hg2 (mul_mem hh2 hg1)
  · have h : ((g⁻¹ * h * g : (Module.End F V)ˣ) : Module.End F V) - 1 =
        ((g⁻¹ : (Module.End F V)ˣ) : Module.End F V) * ((h : Module.End F V) - 1) *
          (g : Module.End F V) := by
      simp only [Units.val_mul, mul_sub, sub_mul, mul_one, Units.inv_mul]
    rw [h]
    have h1 := 𝓛.mul_mem_endFiltration ((𝓛.mem_order_iff_mem_endFiltration).1 hg2) hh3
    have h2 := 𝓛.mul_mem_endFiltration h1 ((𝓛.mem_order_iff_mem_endFiltration).1 hg1)
    simpa using h2

/-- If `g, h ∈ U^0(𝔄)` and `h - g ∈ 𝔓^j`, then `g⁻¹ h ∈ U^j(𝔄)`. -/
theorem inv_mul_mem_unitFiltration {g h : (Module.End F V)ˣ} (hg : g ∈ 𝓛.unitFiltration 0)
    (hh : h ∈ 𝓛.unitFiltration 0) {j : ℕ}
    (hgh : (h : Module.End F V) - g ∈ 𝓛.endFiltration j) : g⁻¹ * h ∈ 𝓛.unitFiltration j := by
  obtain ⟨hg1, hg2, -⟩ := hg
  obtain ⟨hh1, hh2, -⟩ := hh
  refine ⟨?_, ?_, ?_⟩
  · simp only [Units.val_mul]
    exact mul_mem hg2 hh1
  · simp only [mul_inv_rev, inv_inv, Units.val_mul]
    exact mul_mem hh2 hg1
  · have h : ((g⁻¹ * h : (Module.End F V)ˣ) : Module.End F V) - 1 =
        ((g⁻¹ : (Module.End F V)ˣ) : Module.End F V) * ((h : Module.End F V) - g) := by
      simp only [Units.val_mul, mul_sub, Units.inv_mul]
    rw [h]
    simpa using 𝓛.mul_mem_endFiltration ((𝓛.mem_order_iff_mem_endFiltration).1 hg2) hgh

end LatticeChain

end Units

/-! ### Common eigenvectors of a finite abelian group -/

section Eigenvector

variable {Q : Type*} [AddCommGroup Q] [Fintype Q] {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- **Common eigenvectors.** Let `Q` be a finite abelian group and `T : Q → End_ℂ(V)` a map
that is a homomorphism on a subspace `W` stable under every `T z`: `T 0 w = w` and
`T (y + z) w = T y (T z w)` for `w ∈ W`. If `W ≠ 0`, some nonzero `v ∈ W` is an eigenvector of
every `T z`, with eigenvalue `χ z` for a character `χ` of `Q`. The vector is one of the
averages `v_χ = ∑_z χ(-z) T z w`, whose sum over all `χ` is `|Q| w`. -/
theorem exists_addChar_eigenvector (T : Q → V →ₗ[ℂ] V) (W : Submodule ℂ V)
    (hW : ∀ z, ∀ w ∈ W, T z w ∈ W) (h0 : ∀ w ∈ W, T 0 w = w)
    (hmul : ∀ y z, ∀ w ∈ W, T (y + z) w = T y (T z w)) {w : V} (hw : w ∈ W) (hw0 : w ≠ 0) :
    ∃ χ : AddChar Q ℂ, ∃ v ∈ W, v ≠ 0 ∧ ∀ z, T z v = χ z • v := by
  classical
  let vχ : AddChar Q ℂ → V := fun χ => ∑ z, χ (-z) • T z w
  have hmem : ∀ χ, vχ χ ∈ W := fun χ =>
    Submodule.sum_mem _ fun z _ => W.smul_mem _ (hW z w hw)
  have heig : ∀ χ y, T y (vχ χ) = χ y • vχ χ := by
    intro χ y
    calc T y (vχ χ) = ∑ z, χ (-z) • T (y + z) w := by
          simp only [vχ, map_sum, map_smul]
          exact Finset.sum_congr rfl fun z _ => by rw [hmul y z w hw]
      _ = ∑ u, χ (-(u - y)) • T u w :=
          Fintype.sum_equiv (Equiv.addLeft y) _ _ fun z => by simp
      _ = χ y • vχ χ := by
          simp only [vχ, Finset.smul_sum, smul_smul]
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [neg_sub, sub_eq_add_neg, AddChar.map_add_eq_mul]
  have hsum : ∑ χ : AddChar Q ℂ, vχ χ = (Fintype.card Q : ℂ) • w := by
    simp only [vχ]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul, AddChar.sum_apply_eq_ite, neg_eq_zero, ite_smul, zero_smul,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, h0 w hw]
  have hne : ∑ χ : AddChar Q ℂ, vχ χ ≠ 0 := by
    rw [hsum]
    exact smul_ne_zero (Nat.cast_ne_zero.2 Fintype.card_ne_zero) hw0
  obtain ⟨χ, -, hχ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  exact ⟨χ, vχ χ, hmem χ, hχ, heig χ⟩

end Eigenvector

theorem mem_fixedVectors_iff_forall_mem {R G V : Type*} [CommRing R] [Group G]
    [AddCommGroup V] [Module R V] (ρ : Representation R G V) (H : Subgroup G) (v : V) :
    v ∈ fixedVectors ρ H ↔ ∀ g ∈ H, ρ g v = v := by
  unfold fixedVectors
  rw [Representation.mem_invariants]
  exact ⟨fun h g hg => h ⟨g, hg⟩, fun h g => h g g.2⟩

/-! ### A stratum at every level value -/

section Padic

/-! The canonical instances, as in the Library's normalized-level statement modules, with
explicit names. -/

local instance strExTopologicalSpace {p : ℕ} [Fact p.Prime] (F : PadicField p) :
    TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

local instance strExValuativeRel {p : ℕ} [Fact p.Prime] (F : PadicField p) :
    ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel

local instance strExLocalField {p : ℕ} [Fact p.Prime] (F : PadicField p) :
    IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField

local instance strExTopologicalSpaceGL {p : ℕ} [Fact p.Prime] (F : PadicField p) (n : ℕ) :
    TopologicalSpace (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopology n

/-- **A stratum at every level value** (Bushnell 1987, (3.3) and the proof of Theorem 2′,
printed pp. 196–197). Let `ψ` be an additive character of `K` that is trivial on `𝔭_K` but not
on `𝔬_K`, and let `m ≥ 1`. If the class `a` has a nonzero vector fixed by `U^{m+1}(𝔄(𝓛))`, then
`a` contains a stratum `[𝔄(𝓛), m, m - 1, b]`. -/
theorem exists_containsStratum_of_hasFixedVector {p : ℕ} [Fact p.Prime]
    (K : PadicField.{uK} p) (n : ℕ) (ψ : AddChar K.Carrier ℂ)
    (hψ : ∀ c ∈ 𝓂[K.Carrier], ψ (c : K.Carrier) = 1)
    (hψ' : ∃ c : 𝒪[K.Carrier], ψ (c : K.Carrier) ≠ 1)
    (a : SmoothDualClass.{0, uK, uV} (k := ℂ) (G := GeneralLinear n K.Carrier))
    (𝓛 : LatticeChain 𝒪[K.Carrier] K.Carrier (Fin n → K.Carrier)) {m : ℕ} (hm : 1 ≤ m)
    (hfix : SmoothDualClass.HasFixedVector (unitSubgroup K 𝓛 (m + 1)) a) :
    ∃ b, ContainsStratum K n ψ a 𝓛 m b := by
  classical
  obtain ⟨A, rfl⟩ := Quotient.exists_rep a
  set ρ := A.obj.representation with hρ
  set W := fixedVectors ρ (unitSubgroup K 𝓛 (m + 1)) with hW
  have hW0 : W ≠ ⊥ := hfix
  obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff W).1 hW0
  have hWmem : ∀ v, v ∈ W ↔ ∀ g ∈ unitSubgroup K 𝓛 (m + 1), ρ g v = v :=
    fun v => mem_fixedVectors_iff_forall_mem ρ _ v
  -- units of `End(K^n)` as elements of `GL_n(K)`
  let toG : (Module.End K.Carrier (Fin n → K.Carrier))ˣ → GeneralLinear n K.Carrier :=
    fun u => Matrix.GeneralLinearGroup.toLin.symm u
  have htoG : ∀ u, Matrix.GeneralLinearGroup.toLin (toG u) = u := fun u =>
    Matrix.GeneralLinearGroup.toLin.apply_symm_apply u
  have htoG_mul : ∀ u u', toG (u * u') = toG u * toG u' := fun u u' =>
    map_mul Matrix.GeneralLinearGroup.toLin.symm u u'
  have hmemG : ∀ u j, toG u ∈ unitSubgroup K 𝓛 j ↔ u ∈ 𝓛.unitFiltration j := by
    intro u j
    rw [mem_unitSubgroup, htoG]
  -- congruent units act in the same way on `W`
  have hact : ∀ g h : (Module.End K.Carrier (Fin n → K.Carrier))ˣ,
      g ∈ 𝓛.unitFiltration 0 → h ∈ 𝓛.unitFiltration 0 →
      (h : Module.End K.Carrier (Fin n → K.Carrier)) - g ∈ 𝓛.endFiltration ((m : ℤ) + 1) →
      ∀ v ∈ W, ρ (toG h) v = ρ (toG g) v := by
    intro g h hg hh hgh v hv
    have h1 : g⁻¹ * h ∈ 𝓛.unitFiltration (m + 1) :=
      𝓛.inv_mul_mem_unitFiltration hg hh (by exact_mod_cast hgh)
    have h2 : toG h = toG g * toG (g⁻¹ * h) := by
      rw [← htoG_mul, mul_inv_cancel_left]
    rw [h2, map_mul, Module.End.mul_apply, (hWmem v).1 hv _ ((hmemG _ _).2 h1)]
  -- `W` is stable under `U^0(𝔄)`
  have hstab : ∀ g ∈ 𝓛.unitFiltration 0, ∀ v ∈ W, ρ (toG g) v ∈ W := by
    intro g hg v hv
    rw [hWmem]
    intro t ht
    have h1 : g⁻¹ * Matrix.GeneralLinearGroup.toLin t * g ∈ 𝓛.unitFiltration (m + 1) :=
      𝓛.inv_mul_mul_mem_unitFiltration hg ht
    have h2 : t * toG g = toG g * toG (g⁻¹ * Matrix.GeneralLinearGroup.toLin t * g) := by
      apply Matrix.GeneralLinearGroup.toLin.injective
      rw [map_mul, map_mul, htoG, htoG]
      group
    have h3 : ρ t (ρ (toG g) v) = ρ (t * toG g) v := by
      rw [map_mul, Module.End.mul_apply]
    rw [h3, h2, map_mul, Module.End.mul_apply, (hWmem v).1 hv _ ((hmemG _ _).2 h1)]
  -- residue coordinates of `U^m(𝔄) / U^{m+1}(𝔄)`
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K.Carrier]
  obtain ⟨r, β, hβ, -⟩ := LatticeChain.exists_basis_splits_both hϖ 𝓛 𝓛
  have : Fintype 𝓀[K.Carrier] := Fintype.ofFinite _
  have hX : ∀ z, 𝓛.coordEnd hϖ β m z ∈ 𝓛.endFiltration m := fun z =>
    LatticeChain.coordEnd_mem hϖ hβ m z
  have hunit : ∀ z : Fin r → Fin r → 𝓀[K.Carrier], ∃ g ∈ 𝓛.unitFiltration m,
      (g : Module.End K.Carrier (Fin n → K.Carrier)) = 1 + 𝓛.coordEnd hϖ β m z :=
    fun z => 𝓛.exists_mem_unitFiltration hm (hX z)
  choose f hf hfv using hunit
  have hU0 : ∀ z, f z ∈ 𝓛.unitFiltration 0 := fun z =>
    𝓛.unitFiltration_antitone (Nat.zero_le m) (hf z)
  have h0 : ∀ v ∈ W, ρ (toG (f 0)) v = v := by
    intro v hv
    have h := hact 1 (f 0) (one_mem _) (hU0 0) (by
      rw [hfv, Units.val_one, add_sub_cancel_left]
      exact LatticeChain.coordEnd_zero_mem hϖ hβ m) v hv
    rw [h, show toG 1 = 1 from map_one Matrix.GeneralLinearGroup.toLin.symm, map_one,
      Module.End.one_apply]
  have hmul : ∀ y z, ∀ v ∈ W, ρ (toG (f (y + z))) v = ρ (toG (f y)) (ρ (toG (f z)) v) := by
    intro y z v hv
    have hdiff : ((f y * f z : (Module.End K.Carrier (Fin n → K.Carrier))ˣ) :
        Module.End K.Carrier (Fin n → K.Carrier)) - f (y + z) ∈
          𝓛.endFiltration ((m : ℤ) + 1) := by
      have e : ((f y * f z : (Module.End K.Carrier (Fin n → K.Carrier))ˣ) :
          Module.End K.Carrier (Fin n → K.Carrier)) - f (y + z) =
          (𝓛.coordEnd hϖ β m y + 𝓛.coordEnd hϖ β m z - 𝓛.coordEnd hϖ β m (y + z)) +
            𝓛.coordEnd hϖ β m y * 𝓛.coordEnd hϖ β m z := by
        rw [Units.val_mul, hfv, hfv, hfv]
        noncomm_ring
      rw [e]
      refine add_mem (LatticeChain.coordEnd_add_sub_mem hϖ hβ m y z) ?_
      exact 𝓛.endFiltration_antitone (by omega) (𝓛.mul_mem_endFiltration (hX y) (hX z))
    have h := hact (f (y + z)) (f y * f z) (hU0 _) (mul_mem (hU0 y) (hU0 z)) hdiff v hv
    rw [← h, htoG_mul, map_mul, Module.End.mul_apply]
  -- a common eigenvector
  obtain ⟨χ, v, hv, hv0, hχ⟩ := exists_addChar_eigenvector (fun z => ρ (toG (f z))) W
    (fun z v hv => hstab _ (hU0 z) v hv) h0 hmul hw hw0
  have hχ' : ∀ z, ρ (toG (f z)) v = χ z • v := hχ
  have hχX : ∀ z z', 𝓛.coordEnd hϖ β m z - 𝓛.coordEnd hϖ β m z' ∈
      𝓛.endFiltration ((m : ℤ) + 1) → χ z = χ z' := by
    intro z z' hzz
    have h := hact (f z') (f z) (hU0 _) (hU0 _)
      (by rw [hfv, hfv, add_sub_add_left_eq_sub]; exact hzz) v hv
    rw [hχ', hχ'] at h
    exact smul_left_injective ℂ hv0 h
  -- the character `θ` of `𝔓^m / 𝔓^{m+1}`
  have hz : ∀ x : Module.End K.Carrier (Fin n → K.Carrier), ∃ z : Fin r → Fin r → 𝓀[K.Carrier],
      x ∈ 𝓛.endFiltration m → x - 𝓛.coordEnd hϖ β m z ∈ 𝓛.endFiltration ((m : ℤ) + 1) := by
    intro x
    by_cases hx : x ∈ 𝓛.endFiltration m
    · obtain ⟨z, hz⟩ := LatticeChain.exists_sub_coordEnd_mem hϖ hβ hx
      exact ⟨z, fun _ => hz⟩
    · exact ⟨0, fun h => absurd h hx⟩
  choose Z hZ using hz
  obtain ⟨b, hb, hθ⟩ := 𝓛.exists_mem_endFiltration_forall_eq ψ hψ hψ' m (fun x => χ (Z x))
    (by
      intro x hx y hy
      have e : 𝓛.coordEnd hϖ β m (Z (x + y)) - 𝓛.coordEnd hϖ β m (Z x + Z y) =
          -((x + y) - 𝓛.coordEnd hϖ β m (Z (x + y))) + (x - 𝓛.coordEnd hϖ β m (Z x)) +
            (y - 𝓛.coordEnd hϖ β m (Z y)) + (𝓛.coordEnd hϖ β m (Z x) +
              𝓛.coordEnd hϖ β m (Z y) - 𝓛.coordEnd hϖ β m (Z x + Z y)) := by
        abel
      have hmem : 𝓛.coordEnd hϖ β m (Z (x + y)) - 𝓛.coordEnd hϖ β m (Z x + Z y) ∈
          𝓛.endFiltration ((m : ℤ) + 1) := by
        rw [e]
        exact add_mem (add_mem (add_mem (neg_mem (hZ _ (add_mem hx hy))) (hZ x hx)) (hZ y hy))
          (LatticeChain.coordEnd_add_sub_mem hϖ hβ m _ _)
      change χ (Z (x + y)) = χ (Z x) * χ (Z y)
      rw [hχX _ _ hmem, AddChar.map_add_eq_mul])
    (by
      intro x hx
      have hxm : x ∈ 𝓛.endFiltration m := 𝓛.endFiltration_antitone (by omega) hx
      have hmem : 𝓛.coordEnd hϖ β m (Z x) - 𝓛.coordEnd hϖ β m 0 ∈
          𝓛.endFiltration ((m : ℤ) + 1) := by
        have e : 𝓛.coordEnd hϖ β m (Z x) - 𝓛.coordEnd hϖ β m 0 =
            -(x - 𝓛.coordEnd hϖ β m (Z x)) + x - 𝓛.coordEnd hϖ β m 0 := by
          abel
        rw [e]
        exact sub_mem (add_mem (neg_mem (hZ x hxm)) hx) (LatticeChain.coordEnd_zero_mem hϖ hβ m)
      change χ (Z x) = 1
      rw [hχX _ _ hmem, AddChar.map_zero_eq_one])
  -- the stratum
  refine ⟨b, ?_⟩
  unfold ContainsStratum
  refine ⟨hm, hb, A, rfl, v, hv0, fun g hg => ?_⟩
  change ρ g v = _
  set u := Matrix.GeneralLinearGroup.toLin g with hu
  have hg' : u ∈ 𝓛.unitFiltration m := hg
  have hgu : g = toG u := (Matrix.GeneralLinearGroup.toLin.symm_apply_apply g).symm
  have hx : (u : Module.End K.Carrier (Fin n → K.Carrier)) - 1 ∈ 𝓛.endFiltration m := hg'.2.2
  have h := hact (f (Z ((u : Module.End K.Carrier (Fin n → K.Carrier)) - 1))) u (hU0 _)
    (𝓛.unitFiltration_antitone (Nat.zero_le m) hg') (by
      rw [hfv, ← sub_sub]
      exact hZ _ hx) v hv
  rw [hgu, h, hχ', elementCharacter_apply, traceCharacter_apply, ← hθ _ hx]

/-- **Bushnell 1987, Theorem 2′** (printed pp. 196–197). Let `ψ` be an additive character of `K`
that is trivial on `𝔭_K` but not on `𝔬_K`. If the class `a` has positive normalized level `x`,
then there are a lattice chain `𝓛` and `m ≥ 1` with `x = m / e(𝓛)` such that `a` contains a
stratum `[𝔄(𝓛), m, m - 1, b]`, and this stratum is fundamental: `b + y` is not nilpotent for
any `y ∈ 𝔓^{1-m}(𝓛)`. -/
theorem exists_containsStratum_of_isNormalizedLevel {p : ℕ} [Fact p.Prime]
    (K : PadicField.{uK} p) (n : ℕ) (ψ : AddChar K.Carrier ℂ)
    (hψ : ∀ c ∈ 𝓂[K.Carrier], ψ (c : K.Carrier) = 1)
    (hψ' : ∃ c : 𝒪[K.Carrier], ψ (c : K.Carrier) ≠ 1)
    (a : SmoothDualClass.{0, uK, uV} (k := ℂ) (G := GeneralLinear n K.Carrier)) {x : ℚ}
    (hlev : IsNormalizedLevel K n a x) (hx : 0 < x) :
    ∃ (𝓛 : LatticeChain 𝒪[K.Carrier] K.Carrier (Fin n → K.Carrier)) (m : ℕ)
      (b : Module.End K.Carrier (Fin n → K.Carrier)),
      x = (m : ℚ) / (𝓛.period : ℚ) ∧ ContainsStratum K n ψ a 𝓛 m b ∧
        ∀ y ∈ 𝓛.endFiltration (1 - (m : ℤ)), ¬ IsNilpotent (b + y) := by
  obtain ⟨𝓛, m, hxm, hfix⟩ := hlev.1
  have hm : 1 ≤ m := by
    refine Nat.one_le_iff_ne_zero.2 ?_
    rintro rfl
    simp only [Nat.cast_zero, zero_div] at hxm
    linarith
  obtain ⟨b, hb⟩ := exists_containsStratum_of_hasFixedVector K n ψ hψ hψ' a 𝓛 hm hfix
  refine ⟨𝓛, m, b, hxm, hb, ?_⟩
  subst hxm
  exact not_isNilpotent_of_isNormalizedLevel K n ψ hψ a 𝓛 m b hb hlev

end Padic

end Langlands.BushnellKutzko
