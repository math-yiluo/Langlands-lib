import Langlands.BushnellKutzko.RadicalFiltrationProof
import Langlands.BushnellKutzko.Stratum

/-! # Equivalent strata: order, depth and level (BK93 (1.5.2), p. 43)

Helper results for `StratumEquivalenceStatement`: two equivalent strata over a
nonarchimedean local field have the same filtration `n ↦ 𝔓^n`, hence the same order and
the same `r`, and the same `n` when the parameters have exact level.
-/

open ValuativeRel

namespace Langlands.BushnellKutzko

namespace StratumEquivalence

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]

/-- `𝔓^m 𝔓^n = 𝔓^{m+n}` (first item of `radicalFiltration`). -/
theorem endFiltration_mul_eq (𝓛 : LatticeChain 𝒪[F] F V) (m n : ℤ) :
    𝓛.endFiltration m * 𝓛.endFiltration n = 𝓛.endFiltration (m + n) :=
  (radicalFiltration F V 𝓛).1 m n

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- `1 ∈ 𝔓^0`. -/
theorem one_mem_endFiltration_zero (𝓛 : LatticeChain 𝒪[F] F V) :
    (1 : Module.End F V) ∈ 𝓛.endFiltration 0 :=
  (𝓛.mem_order_iff_mem_endFiltration).1 (one_mem 𝓛.order)

/-- The colon description of the filtration: `𝔓^m = {x : x 𝔓^n ⊆ 𝔓^{m+n}}` for every `n`. -/
theorem mem_endFiltration_iff_mul (𝓛 : LatticeChain 𝒪[F] F V) (m n : ℤ)
    (x : Module.End F V) :
    x ∈ 𝓛.endFiltration m ↔ ∀ y ∈ 𝓛.endFiltration n, x * y ∈ 𝓛.endFiltration (m + n) := by
  constructor
  · intro hx y hy
    exact 𝓛.mul_mem_endFiltration hx hy
  · intro h
    have h1 : (1 : Module.End F V) ∈ 𝓛.endFiltration n * 𝓛.endFiltration (-n) := by
      rw [endFiltration_mul_eq, add_neg_cancel]
      exact one_mem_endFiltration_zero 𝓛
    have hle : 𝓛.endFiltration n * 𝓛.endFiltration (-n) ≤
        (𝓛.endFiltration m).comap (LinearMap.mulLeft 𝒪[F] x) := by
      rw [Submodule.mul_le]
      intro p hp q hq
      rw [Submodule.mem_comap, LinearMap.mulLeft_apply, ← mul_assoc]
      have := 𝓛.mul_mem_endFiltration (h p hp) hq
      rwa [add_neg_cancel_right] at this
    simpa using hle h1

/-- If some filtration steps of two chains agree, then their orders `𝔓^0` agree. -/
theorem endFiltration_zero_eq {𝓛₁ 𝓛₂ : LatticeChain 𝒪[F] F V} {a c : ℤ}
    (h : 𝓛₁.endFiltration a = 𝓛₂.endFiltration c) :
    𝓛₁.endFiltration 0 = 𝓛₂.endFiltration 0 := by
  ext x
  rw [mem_endFiltration_iff_mul 𝓛₁ 0 a, mem_endFiltration_iff_mul 𝓛₂ 0 c, zero_add, zero_add, h]

/-- `𝔓^1` is the set of elements of the order lying in its Jacobson radical. -/
theorem mem_endFiltration_one_iff (𝓛 : LatticeChain 𝒪[F] F V) (x : Module.End F V) :
    x ∈ 𝓛.endFiltration 1 ↔
      ∃ hx : x ∈ 𝓛.order, (⟨x, hx⟩ : 𝓛.order) ∈ Ring.jacobson 𝓛.order := by
  constructor
  · intro hx
    have hx0 : x ∈ 𝓛.order :=
      (𝓛.mem_order_iff_mem_endFiltration).2 (𝓛.endFiltration_antitone (by norm_num) hx)
    exact ⟨hx0, ((radicalFiltration F V 𝓛).2.2.2.1 ⟨x, hx0⟩).2 hx⟩
  · rintro ⟨hx0, hj⟩
    exact ((radicalFiltration F V 𝓛).2.2.2.1 ⟨x, hx0⟩).1 hj

/-- Chains with the same order have the same `𝔓^1`. -/
theorem endFiltration_one_eq {𝓛₁ 𝓛₂ : LatticeChain 𝒪[F] F V}
    (h : 𝓛₁.endFiltration 0 = 𝓛₂.endFiltration 0) :
    𝓛₁.endFiltration 1 = 𝓛₂.endFiltration 1 := by
  have ho : 𝓛₁.order = 𝓛₂.order := by
    apply SetLike.coe_injective
    show ((𝓛₁.endFiltration 0 : Submodule 𝒪[F] (Module.End F V)) : Set (Module.End F V)) =
      ((𝓛₂.endFiltration 0 : Submodule 𝒪[F] (Module.End F V)) : Set (Module.End F V))
    rw [h]
  ext x
  rw [mem_endFiltration_one_iff 𝓛₁, mem_endFiltration_one_iff 𝓛₂, ho]

/-- If some filtration steps of two chains agree, then all filtration steps agree. -/
theorem endFiltration_eq_of_eq {𝓛₁ 𝓛₂ : LatticeChain 𝒪[F] F V} {a c : ℤ}
    (h : 𝓛₁.endFiltration a = 𝓛₂.endFiltration c) :
    𝓛₁.endFiltration = 𝓛₂.endFiltration := by
  have h0 := endFiltration_zero_eq h
  have h1 := endFiltration_one_eq h0
  have hnat : ∀ k : ℕ, 𝓛₁.endFiltration k = 𝓛₂.endFiltration k := by
    intro k
    induction k with
    | zero => simpa using h0
    | succ k ih =>
      push_cast
      rw [← endFiltration_mul_eq 𝓛₁ k 1, ← endFiltration_mul_eq 𝓛₂ k 1, ih, h1]
  funext k
  rcases le_or_gt 0 k with hk | hk
  · obtain ⟨k', rfl⟩ := Int.eq_ofNat_of_zero_le hk
    exact hnat k'
  · ext x
    obtain ⟨k', hk'⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ -k)
    rw [mem_endFiltration_iff_mul 𝓛₁ k (-k), mem_endFiltration_iff_mul 𝓛₂ k (-k),
      add_neg_cancel, h0, hk', hnat k']

/-- The filtration `n ↦ 𝔓^n` of a chain is injective. -/
theorem endFiltration_injective (𝓛 : LatticeChain 𝒪[F] F V) :
    Function.Injective 𝓛.endFiltration := by
  intro a c h
  by_contra hne
  wlog hlt : a < c generalizing a c
  · exact this h.symm (Ne.symm hne) (by omega)
  have h0 : 𝓛.endFiltration 0 = 𝓛.endFiltration (c - a) := by
    calc 𝓛.endFiltration 0 = 𝓛.endFiltration (a + -a) := by rw [add_neg_cancel]
      _ = 𝓛.endFiltration a * 𝓛.endFiltration (-a) := (endFiltration_mul_eq 𝓛 a (-a)).symm
      _ = 𝓛.endFiltration c * 𝓛.endFiltration (-a) := by rw [h]
      _ = 𝓛.endFiltration (c - a) := by rw [endFiltration_mul_eq, sub_eq_add_neg]
  have h1 : (1 : Module.End F V) ∈ 𝓛.endFiltration 1 := by
    have : (1 : Module.End F V) ∈ 𝓛.endFiltration (c - a) :=
      h0 ▸ one_mem_endFiltration_zero 𝓛
    exact 𝓛.endFiltration_antitone (by omega) this
  apply (𝓛.lattice_succ_lt 0).not_ge
  intro v hv
  simpa using h1 0 v hv

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- Equivalent strata have the same lattice `𝔓^{-r}` (the coset `b + 𝔓^{-r}` determines its
underlying additive subgroup). -/
theorem endFiltration_neg_r_eq {S T : Stratum 𝒪[F] F V} (h : S.Equivalent T) :
    S.chain.endFiltration (-S.r) = T.chain.endFiltration (-T.r) := by
  have hS : ∀ x, x ∈ S.coset ↔ x - S.b ∈ S.chain.endFiltration (-S.r) := fun _ => Iff.rfl
  have hT : ∀ x, x ∈ T.coset ↔ x - T.b ∈ T.chain.endFiltration (-T.r) := fun _ => Iff.rfl
  have hb : S.b - T.b ∈ T.chain.endFiltration (-T.r) := by
    rw [← hT, ← h, hS, sub_self]
    exact zero_mem _
  ext x
  have key : x ∈ S.chain.endFiltration (-S.r) ↔ x + S.b ∈ S.coset := by
    rw [hS, add_sub_cancel_right]
  rw [key, show S.coset = T.coset from h, hT]
  constructor
  · intro hx
    have := sub_mem hx hb
    rwa [show x + S.b - T.b - (S.b - T.b) = x by abel] at this
  · intro hx
    have := add_mem hx hb
    rwa [show x + (S.b - T.b) = x + S.b - T.b by abel] at this

/-- Equivalent strata have the same filtration `n ↦ 𝔓^n`. -/
theorem endFiltration_eq_of_equivalent {S T : Stratum 𝒪[F] F V} (h : S.Equivalent T) :
    S.chain.endFiltration = T.chain.endFiltration :=
  endFiltration_eq_of_eq (endFiltration_neg_r_eq h)

/-- Equivalent strata have the same order. -/
theorem order_eq_of_equivalent {S T : Stratum 𝒪[F] F V} (h : S.Equivalent T) :
    S.chain.order = T.chain.order := by
  have h0 := congrFun (endFiltration_eq_of_equivalent h) 0
  apply SetLike.coe_injective
  show ((S.chain.endFiltration 0 : Submodule 𝒪[F] (Module.End F V)) :
      Set (Module.End F V)) =
    ((T.chain.endFiltration 0 : Submodule 𝒪[F] (Module.End F V)) : Set (Module.End F V))
  rw [h0]

/-- Equivalent strata have the same `r`. -/
theorem r_eq_of_equivalent {S T : Stratum 𝒪[F] F V} (h : S.Equivalent T) : S.r = T.r := by
  have h1 := endFiltration_neg_r_eq h
  rw [endFiltration_eq_of_equivalent h] at h1
  have := endFiltration_injective T.chain h1
  omega

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The coset condition: `b_S - b_T ∈ 𝔓^{-r}` for equivalent strata. -/
theorem sub_mem_of_equivalent {S T : Stratum 𝒪[F] F V} (h : S.Equivalent T) :
    S.b - T.b ∈ T.chain.endFiltration (-T.r) := by
  have hS : S.b ∈ S.coset := by
    show S.b - S.b ∈ S.chain.endFiltration (-S.r)
    rw [sub_self]
    exact zero_mem _
  have : S.b ∈ T.coset := by
    rw [← show S.coset = T.coset from h]
    exact hS
  exact this

/-- If `v_𝔄(x) = m`, then `x ∈ 𝔓^m` and `m` is the largest such index. -/
theorem mem_of_valuation_eq {𝓛 : LatticeChain 𝒪[F] F V} {x : Module.End F V} {m : ℤ}
    (hv : 𝓛.valuation x = (m : WithTop ℤ)) :
    x ∈ 𝓛.endFiltration m ∧ ∀ k, x ∈ 𝓛.endFiltration k → k ≤ m := by
  have hx : x ≠ 0 := by
    rintro rfl
    rw [LatticeChain.valuation_zero] at hv
    exact WithTop.top_ne_coe hv
  obtain ⟨hne, hbdd⟩ := (radicalFiltration F V 𝓛).2.2.2.2 x hx
  have hs : sSup {n : ℤ | x ∈ 𝓛.endFiltration n} = m := by
    unfold LatticeChain.valuation at hv
    simp only [hx, ↓reduceIte] at hv
    exact_mod_cast hv
  refine ⟨?_, fun k hk => ?_⟩
  · rw [← hs]
    exact Int.csSup_mem hne hbdd
  · rw [← hs]
    exact le_csSup hbdd hk

/-- Level comparison: if `v_𝔄(x) = -n`, `v_𝔄(y) = -n'`, `r < n` and `x - y ∈ 𝔓^{-r}`,
then `n' ≤ n`. -/
theorem le_of_valuation_eq {𝓛 : LatticeChain 𝒪[F] F V} {x y : Module.End F V} {n n' r : ℤ}
    (hr : r < n) (hx : 𝓛.valuation x = ((-n : ℤ) : WithTop ℤ))
    (hy : 𝓛.valuation y = ((-n' : ℤ) : WithTop ℤ))
    (hxy : x - y ∈ 𝓛.endFiltration (-r)) : n' ≤ n := by
  have hxm := (mem_of_valuation_eq hx).1
  have hy' : y ∈ 𝓛.endFiltration (-n) := by
    rw [show y = x - (x - y) by abel]
    exact sub_mem hxm (𝓛.endFiltration_antitone (by omega) hxy)
  have := (mem_of_valuation_eq hy).2 _ hy'
  omega

/-- Equivalent strata whose parameters have exact level have the same `n`. -/
theorem n_eq_of_equivalent {S T : Stratum 𝒪[F] F V} (h : S.Equivalent T)
    (hv : S.chain.valuation S.b = (-S.n : WithTop ℤ) ∧
      T.chain.valuation T.b = (-T.n : WithTop ℤ)) : S.n = T.n := by
  have hP := endFiltration_eq_of_equivalent h
  have hval : S.chain.valuation = T.chain.valuation := by
    funext x
    unfold LatticeChain.valuation
    rw [hP]
  have hS : T.chain.valuation S.b = ((-S.n : ℤ) : WithTop ℤ) := by
    rw [← hval, hv.1]
    push_cast
    rfl
  have hT : T.chain.valuation T.b = ((-T.n : ℤ) : WithTop ℤ) := by
    rw [hv.2]
    push_cast
    rfl
  have hr := r_eq_of_equivalent h
  have hsub := sub_mem_of_equivalent h
  have h1 : T.n ≤ S.n := le_of_valuation_eq (by have := S.r_lt_n; omega) hS hT hsub
  have h2 : S.n ≤ T.n := le_of_valuation_eq T.r_lt_n hT hS
    (by rw [show T.b - S.b = -(S.b - T.b) by abel]; exact neg_mem hsub)
  omega

end StratumEquivalence

end Langlands.BushnellKutzko
