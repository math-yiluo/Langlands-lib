import Langlands.BushnellKutzko.MoyReduction
import Langlands.BushnellKutzko.FundamentalStratumDual
import Langlands.BushnellKutzko.NormalizedLevel

/-! # A stratum contained at a lattice chain attaining the level is fundamental

Bushnell (1987), Theorem 2′(ii) and its proof from Theorem 1 (printed pp. 196–197). Theorem 1 is
Bushnell–Kutzko (1993), (2.3.1), printed p. 57, where fundamental strata are defined.

Let `a` be a class of irreducible admissible representations of `GL_n(K)` with normalized level
`m / e(𝓛)`, attained at the lattice chain `𝓛`. If `a` contains a stratum `[𝔄(𝓛), m, m - 1, b]`,
then no element `z` of the coset `b + 𝔓^{1-m}(𝓛)` satisfies `z^k ∈ 𝔓^{1-km}(𝓛)` for any `k`
(`pow_add_not_mem_of_isNormalizedLevel`). In particular the stratum is fundamental: the coset
contains no nilpotent element (`not_isNilpotent_of_isNormalizedLevel`).

Proof. Suppose that `(b + y)^k ∈ 𝔓^{1-km}(𝓛)` with `y ∈ 𝔓^{1-m}(𝓛)`. Moy's reduction
(`LatticeChain.exists_latticeChain_of_pow_mem`) gives a lattice chain `𝓜` and `l ∈ ℕ` with
`l / e(𝓜) < m / e(𝓛)` and `b + 𝔓^{1-m}(𝓛) ⊆ 𝔓^{-l}(𝓜)`
(`LatticeChain.exists_latticeChain_of_pow_add_mem`). Then `𝔓^{1-m}(𝓛) ⊆ 𝔓^{-l}(𝓜)`, and the
trace duality of the filtrations (`LatticeChain.endFiltration_one_sub_le`) gives
`𝔓^{l+1}(𝓜) ⊆ 𝔓^m(𝓛)`, so `U^{l+1}(𝔄(𝓜)) ⊆ U^m(𝔄(𝓛))`. On `U^{l+1}(𝔄(𝓜))` the function
`g ↦ ψ(tr(b(g - 1)))` is trivial, because `b(g - 1) ∈ 𝔓^1(𝓜)` has trace in `𝔭_K`. Hence the
eigenvector of the stratum is fixed by `U^{l+1}(𝔄(𝓜))`, so `l / e(𝓜)` is a normalized level
value of `a`. This contradicts the minimality of `m / e(𝓛)`.
-/

noncomputable section

open ValuativeRel

namespace Langlands.BushnellKutzko

universe u uK uV

/-! ### Traces of elements of `𝔓^1` and the duality of the filtrations -/

section Duality

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ)
variable {ι : Type*} [Fintype ι]

include hϖ in
theorem ordOf_uniformizer : ordOf hϖ (ϖ : F) = 1 := by
  simpa using ordOf_zpow hϖ 1

namespace LatticeChain

include hϖ in
/-- The trace of an element of `𝔓^1(𝓛)` lies in `𝔭_F`, in the form `ϖ⁻¹ tr x ∈ 𝔬_F`. -/
theorem inv_uniformizer_mul_trace_mem (𝓛 : LatticeChain 𝒪[F] F (ι → F))
    {x : Module.End F (ι → F)} (hx : x ∈ 𝓛.endFiltration 1) :
    (ϖ : F)⁻¹ * LinearMap.trace F (ι → F) x ∈ 𝒪[F] := by
  classical
  obtain ⟨r, β, hβ, -⟩ := exists_basis_splits_both hϖ 𝓛 𝓛
  rw [LinearMap.trace_eq_matrix_trace F β x, Matrix.trace, Finset.mul_sum]
  refine sum_mem fun k _ => ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
  change (ϖ : F)⁻¹ * entry β x k k ∈ 𝒪[F]
  by_cases hk : entry β x k k = 0
  · rw [hk, mul_zero]
    exact zero_mem _
  · have h := 𝓛.le_of_mem_endFiltration hϖ hβ hx k k hk
    have he : (0 : ℤ) < 𝓛.period := by exact_mod_cast 𝓛.period_pos
    have h1 : 1 ≤ ordOf hϖ (entry β x k k) := by
      by_contra hcon
      have h0 : ordOf hϖ (entry β x k k) ≤ 0 := by omega
      nlinarith
    have hϖ0 := coe_uniformizer_ne_zero hϖ
    refine mem_integer_of_ordOf_nonneg hϖ (mul_ne_zero (inv_ne_zero hϖ0) hk) ?_
    rw [ordOf_mul hϖ (inv_ne_zero hϖ0) hk, ordOf_inv hϖ hϖ0, ordOf_uniformizer hϖ]
    omega

include hϖ in
/-- If `ψ` is trivial on `𝔭_F`, then `ψ(tr x) = 1` for every `x ∈ 𝔓^1(𝓛)`. -/
theorem addChar_trace_eq_one_of_mem_one (𝓛 : LatticeChain 𝒪[F] F (ι → F)) (ψ : AddChar F ℂ)
    (hψ : ∀ a ∈ 𝓂[F], ψ (a : F) = 1) {x : Module.End F (ι → F)}
    (hx : x ∈ 𝓛.endFiltration 1) : ψ (LinearMap.trace F (ι → F) x) = 1 := by
  have h := 𝓛.inv_uniformizer_mul_trace_mem hϖ hx
  have hϖ0 := coe_uniformizer_ne_zero hϖ
  have hmem : ϖ * (⟨_, h⟩ : 𝒪[F]) ∈ 𝓂[F] :=
    Ideal.mul_mem_right _ _ ((IsLocalRing.mem_maximalIdeal _).2 hϖ.not_isUnit)
  have hc : ((ϖ * (⟨_, h⟩ : 𝒪[F]) : 𝒪[F]) : F) = LinearMap.trace F (ι → F) x := by
    change (ϖ : F) * ((ϖ : F)⁻¹ * _) = _
    rw [← mul_assoc, mul_inv_cancel₀ hϖ0, one_mul]
  rw [← hc]
  exact hψ _ hmem

include hϖ in
/-- **Duality of the filtrations.** For lattice chains `𝓛, 𝓜` in `F^ι` and integers `a, b`,
`𝔓^a(𝓛) ⊆ 𝔓^b(𝓜)` implies `𝔓^{1-b}(𝓜) ⊆ 𝔓^{1-a}(𝓛)`. This is the inclusion of BK93 (1.1.4)
`(𝔓^n)^* = 𝔓^{1-n}` that is used below, for the trace pairing modulo `𝔭_F`. -/
theorem endFiltration_one_sub_le (𝓛 𝓜 : LatticeChain 𝒪[F] F (ι → F)) {a b : ℤ}
    (h : 𝓛.endFiltration a ≤ 𝓜.endFiltration b) :
    𝓜.endFiltration (1 - b) ≤ 𝓛.endFiltration (1 - a) := by
  classical
  intro w hw
  obtain ⟨r, β, hβ, -⟩ := exists_basis_splits_both hϖ 𝓛 𝓛
  rw [← sum_elementaryEnd_entry β w]
  refine Submodule.sum_mem _ fun k _ => Submodule.sum_mem _ fun l _ => ?_
  by_cases hkl : entry β w k l = 0
  · rw [hkl, elementaryEnd_zero]
    exact zero_mem _
  rw [𝓛.elementaryEnd_mem_iff hϖ hβ k l hkl]
  by_contra hlt
  rw [not_le] at hlt
  have hϖ0 := coe_uniformizer_ne_zero hϖ
  have ht0 : (ϖ : F) ^ (-ordOf hϖ (entry β w k l)) ≠ 0 := zpow_ne_zero _ hϖ0
  -- the test element `E_{lk}(ϖ^{-ord(w_{kl})}) ∈ 𝔓^a(𝓛)`
  have hz : elementaryEnd β l k ((ϖ : F) ^ (-ordOf hϖ (entry β w k l))) ∈
      𝓛.endFiltration a := by
    rw [𝓛.elementaryEnd_mem_iff hϖ hβ l k ht0, ordOf_zpow hϖ, mul_neg]
    linarith
  have hwz := 𝓜.mul_mem_endFiltration hw (h hz)
  rw [show 1 - b + b = 1 by ring] at hwz
  have htr := 𝓜.inv_uniformizer_mul_trace_mem hϖ hwz
  rw [trace_mul_elementaryEnd] at htr
  have hne : (ϖ : F) ^ (-ordOf hϖ (entry β w k l)) * entry β w k l ≠ 0 := mul_ne_zero ht0 hkl
  have hord := ordOf_nonneg hϖ (mul_ne_zero (inv_ne_zero hϖ0) hne) htr
  rw [ordOf_mul hϖ (inv_ne_zero hϖ0) hne, ordOf_inv hϖ hϖ0, ordOf_mul hϖ ht0 hkl,
    ordOf_zpow hϖ, ordOf_uniformizer hϖ] at hord
  omega

end LatticeChain

end Duality

/-! ### Unit groups -/

section Units

variable {F : Type u} [Field F] [ValuativeRel F] {V : Type*} [AddCommGroup V] [Module F V]

namespace LatticeChain

/-- If `𝔓^c(𝓜) ⊆ 𝔓^d(𝓛)` with `d ≥ 1`, then `U^c(𝔄(𝓜)) ⊆ U^d(𝔄(𝓛))`. -/
theorem unitFiltration_le_of_endFiltration_le (𝓛 𝓜 : LatticeChain 𝒪[F] F V) {c d : ℕ}
    (hd : 1 ≤ d) (h : 𝓜.endFiltration c ≤ 𝓛.endFiltration d) :
    𝓜.unitFiltration c ≤ 𝓛.unitFiltration d := by
  have hord : ∀ g ∈ 𝓜.unitFiltration c, (g : Module.End F V) ∈ 𝓛.order := by
    intro g hg
    rw [LatticeChain.mem_order_iff_mem_endFiltration]
    have h1 := 𝓛.endFiltration_antitone (show (0 : ℤ) ≤ d by positivity) (h hg.2.2)
    have h2 := (𝓛.mem_order_iff_mem_endFiltration).1 (one_mem 𝓛.order)
    simpa using add_mem h1 h2
  intro g hg
  exact ⟨hord g hg, hord g⁻¹ (inv_mem hg), h hg.2.2⟩

end LatticeChain

end Units

/-! ### The lattice-theoretic core of Bushnell's Theorem 2′ -/

section Core

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ)
variable {ι : Type*} [Fintype ι]

namespace LatticeChain

include hϖ in
/-- Let `m ≥ 1`, `b ∈ 𝔓^{-m}(𝓛)`, `y ∈ 𝔓^{1-m}(𝓛)` and `(b + y)^k ∈ 𝔓^{1-km}(𝓛)` for some
`k`. Then there are a lattice chain `𝓜` and `l ∈ ℕ` with `l / e(𝓜) < m / e(𝓛)`,
`b ∈ 𝔓^{-l}(𝓜)` and `𝔓^{l+1}(𝓜) ⊆ 𝔓^m(𝓛)`. -/
theorem exists_latticeChain_of_pow_add_mem (𝓛 : LatticeChain 𝒪[F] F (ι → F)) {m : ℤ}
    (hm : 1 ≤ m) {b y : Module.End F (ι → F)} (hb : b ∈ 𝓛.endFiltration (-m))
    (hy : y ∈ 𝓛.endFiltration (1 - m)) {k : ℕ}
    (hpow : (b + y) ^ k ∈ 𝓛.endFiltration (k * (-m) + 1)) :
    ∃ (𝓜 : LatticeChain 𝒪[F] F (ι → F)) (l : ℕ), (l : ℤ) * 𝓛.period < m * 𝓜.period ∧
      b ∈ 𝓜.endFiltration (-(l : ℤ)) ∧ 𝓜.endFiltration ((l : ℤ) + 1) ≤ 𝓛.endFiltration m := by
  obtain ⟨𝓜, j', hcos, hlt⟩ := 𝓛.exists_latticeChain_of_pow_mem hb hpow
    (by rw [add_sub_cancel_left, show -m + 1 = 1 - m by ring]; exact hy)
  have he : (0 : ℤ) < 𝓛.period := by exact_mod_cast 𝓛.period_pos
  have he' : (0 : ℤ) < 𝓜.period := by exact_mod_cast 𝓜.period_pos
  have hl : -(((-j').toNat : ℕ) : ℤ) ≤ j' := by omega
  have hcos' : ∀ z, z - b ∈ 𝓛.endFiltration (-m + 1) →
      z ∈ 𝓜.endFiltration (-(((-j').toNat : ℕ) : ℤ)) :=
    fun z hz => 𝓜.endFiltration_antitone hl (hcos z hz)
  refine ⟨𝓜, (-j').toNat, ?_, hcos' b (by simp), ?_⟩
  · rcases le_or_gt 0 j' with h0 | h0
    · rw [show (-j').toNat = 0 by omega]
      push_cast
      nlinarith
    · rw [show (((-j').toNat : ℕ) : ℤ) = -j' by omega]
      nlinarith
  · have hdual : 𝓛.endFiltration (1 - m) ≤ 𝓜.endFiltration (-(((-j').toNat : ℕ) : ℤ)) := by
      intro z hz
      have h1 := hcos' (b + z)
        (by rw [add_sub_cancel_left, show -m + 1 = 1 - m by ring]; exact hz)
      have h2 := hcos' b (by simp)
      simpa using sub_mem h1 h2
    have h := endFiltration_one_sub_le hϖ 𝓛 𝓜 hdual
    rwa [show (1 : ℤ) - -(((-j').toNat : ℕ) : ℤ) = (((-j').toNat : ℕ) : ℤ) + 1 by ring,
      show (1 : ℤ) - (1 - m) = m by ring] at h

include hϖ in
/-- Let `m ≥ 1`, `b ∈ 𝔓^{-m}(𝓛)`, `y ∈ 𝔓^{1-m}(𝓛)` and `b + y` nilpotent. Then there are a
lattice chain `𝓜` and `l ∈ ℕ` with `l / e(𝓜) < m / e(𝓛)`, `b ∈ 𝔓^{-l}(𝓜)` and
`𝔓^{l+1}(𝓜) ⊆ 𝔓^m(𝓛)`. -/
theorem exists_latticeChain_of_isNilpotent_add (𝓛 : LatticeChain 𝒪[F] F (ι → F)) {m : ℤ}
    (hm : 1 ≤ m) {b y : Module.End F (ι → F)} (hb : b ∈ 𝓛.endFiltration (-m))
    (hy : y ∈ 𝓛.endFiltration (1 - m)) (hnil : IsNilpotent (b + y)) :
    ∃ (𝓜 : LatticeChain 𝒪[F] F (ι → F)) (l : ℕ), (l : ℤ) * 𝓛.period < m * 𝓜.period ∧
      b ∈ 𝓜.endFiltration (-(l : ℤ)) ∧ 𝓜.endFiltration ((l : ℤ) + 1) ≤ 𝓛.endFiltration m := by
  obtain ⟨k, hk⟩ := hnil
  exact 𝓛.exists_latticeChain_of_pow_add_mem hϖ hm hb hy (k := k)
    (by rw [hk]; exact zero_mem _)

end LatticeChain

end Core

/-! ### Bushnell's Theorem 2′ for `GL_n(K)` -/

section Padic

/-! The canonical instances, as in the Library's normalized-level statement modules. They have
explicit names, so that importing this module next to those statement modules creates no
clash of automatically generated instance names. -/

local instance lvlAttTopologicalSpace {p : ℕ} [Fact p.Prime] (F : PadicField p) :
    TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

local instance lvlAttValuativeRel {p : ℕ} [Fact p.Prime] (F : PadicField p) :
    ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel

local instance lvlAttLocalField {p : ℕ} [Fact p.Prime] (F : PadicField p) :
    IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField

local instance lvlAttTopologicalSpaceGL {p : ℕ} [Fact p.Prime] (F : PadicField p) (n : ℕ) :
    TopologicalSpace (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopology n

/-- **Bushnell 1987, Theorem 2′(ii)**, for strata given by elements, in the strong form that
the proof gives. Let `ψ` be an additive character of `K` that is trivial on `𝔭_K`, and let `a` be
a class of irreducible admissible representations of `GL_n(K)` whose normalized level is
`m / e(𝓛)`. If `a` contains the stratum `[𝔄(𝓛), m, m - 1, b]`, then `(b + y)^k ∉ 𝔓^{1-km}(𝓛)`
for every `y ∈ 𝔓^{1-m}(𝓛)` and every `k ∈ ℕ`. -/
theorem pow_add_not_mem_of_isNormalizedLevel {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)
    (n : ℕ) (ψ : AddChar K.Carrier ℂ) (hψ : ∀ c ∈ 𝓂[K.Carrier], ψ (c : K.Carrier) = 1)
    (a : SmoothDualClass.{0, uK, uV} (k := ℂ) (G := GeneralLinear n K.Carrier))
    (𝓛 : LatticeChain 𝒪[K.Carrier] K.Carrier (Fin n → K.Carrier)) (m : ℕ)
    (b : Module.End K.Carrier (Fin n → K.Carrier)) (hcont : ContainsStratum K n ψ a 𝓛 m b)
    (hlev : IsNormalizedLevel K n a ((m : ℚ) / (𝓛.period : ℚ))) :
    ∀ y ∈ 𝓛.endFiltration (1 - (m : ℤ)), ∀ k : ℕ,
      (b + y) ^ k ∉ 𝓛.endFiltration (k * (-(m : ℤ)) + 1) := by
  intro y hy k hpow
  obtain ⟨hm, hb, A, hA, v, hv0, hvχ⟩ := hcont
  subst hA
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K.Carrier]
  obtain ⟨𝓜, l, hlt, hbM, hle⟩ := 𝓛.exists_latticeChain_of_pow_add_mem hϖ (m := m)
    (by exact_mod_cast hm) hb hy hpow
  have hU : 𝓜.unitFiltration (l + 1) ≤ 𝓛.unitFiltration m :=
    𝓛.unitFiltration_le_of_endFiltration_le 𝓜 hm (by exact_mod_cast hle)
  -- the eigenvector `v` is fixed by `U^{l+1}(𝔄(𝓜))`
  have hmem : (l : ℚ) / (𝓜.period : ℚ) ∈ normalizedLevelValues K n (Quotient.mk _ A) := by
    refine ⟨𝓜, l, rfl, ?_⟩
    show fixedVectors A.obj.representation _ ≠ ⊥
    rw [Submodule.ne_bot_iff]
    refine ⟨v, (Representation.mem_invariants _ v).mpr fun g => ?_, hv0⟩
    change A.obj.representation g v = v
    rw [hvχ _ (hU g.2)]
    have h1 := 𝓜.mul_mem_endFiltration hbM g.2.2.2
    rw [show -(l : ℤ) + ((l + 1 : ℕ) : ℤ) = 1 by push_cast; ring] at h1
    have h2 := 𝓜.addChar_trace_eq_one_of_mem_one hϖ ψ hψ h1
    rw [elementCharacter_apply, traceCharacter_apply]
    exact (congrArg (· • v) h2).trans (one_smul _ _)
  -- minimality of the level
  have h := hlev.2 hmem
  have he : (0 : ℚ) < 𝓛.period := by exact_mod_cast 𝓛.period_pos
  have he' : (0 : ℚ) < 𝓜.period := by exact_mod_cast 𝓜.period_pos
  rw [div_le_div_iff₀ he he'] at h
  have hlt' : ((l : ℤ) * 𝓛.period : ℚ) < ((m : ℤ) * 𝓜.period : ℚ) := by exact_mod_cast hlt
  push_cast at hlt'
  linarith

/-- **Bushnell 1987, Theorem 2′(ii)**, for strata given by elements. Let `ψ` be an additive
character of `K` that is trivial on `𝔭_K`, and let `a` be a class of irreducible admissible
representations of `GL_n(K)` whose normalized level is `m / e(𝓛)`. If `a` contains the stratum
`[𝔄(𝓛), m, m - 1, b]`, then the stratum is fundamental: `b + y` is not nilpotent for any
`y ∈ 𝔓^{1-m}(𝓛)`. -/
theorem not_isNilpotent_of_isNormalizedLevel {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)
    (n : ℕ) (ψ : AddChar K.Carrier ℂ) (hψ : ∀ c ∈ 𝓂[K.Carrier], ψ (c : K.Carrier) = 1)
    (a : SmoothDualClass.{0, uK, uV} (k := ℂ) (G := GeneralLinear n K.Carrier))
    (𝓛 : LatticeChain 𝒪[K.Carrier] K.Carrier (Fin n → K.Carrier)) (m : ℕ)
    (b : Module.End K.Carrier (Fin n → K.Carrier)) (hcont : ContainsStratum K n ψ a 𝓛 m b)
    (hlev : IsNormalizedLevel K n a ((m : ℚ) / (𝓛.period : ℚ))) :
    ∀ y ∈ 𝓛.endFiltration (1 - (m : ℤ)), ¬ IsNilpotent (b + y) := by
  intro y hy ⟨k, hk⟩
  exact pow_add_not_mem_of_isNormalizedLevel K n ψ hψ a 𝓛 m b hcont hlev y hy k
    (by rw [hk]; exact zero_mem _)

end Padic

end Langlands.BushnellKutzko
