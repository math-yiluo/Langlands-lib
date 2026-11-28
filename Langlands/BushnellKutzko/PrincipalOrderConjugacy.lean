import Langlands.BushnellKutzko.SplittingBasis
import Langlands.BushnellKutzko.PrincipalChainResidueDegree
import Langlands.BushnellKutzko.SimpleCharacterSequence
import Langlands.BushnellKutzko.StratumSemilinearTransport

/-! # Periods and conjugacy of principal orders (BK93 §1.1, printed pp. 22–23)

For lattice chains over a nonarchimedean local field `F` in a finite-dimensional `F`-space
`V` of dimension `N`:

* `LatticeChain.period_eq_of_order_eq`: two chains with the same order have the same period;
* `LatticeChain.period_dvd_finrank_of_isPrincipalOrder`: the period of a chain whose order is
  principal divides `N`;
* `LatticeChain.exists_order_eq_of_isPrincipalOrder`: two chains with principal orders of the
  same period have conjugate orders.
-/

noncomputable section

open ValuativeRel IsLocalRing

namespace Langlands.BushnellKutzko.LatticeChain

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]

/-! ### The period is determined by the order -/

/-- Multiplication by a uniformizer lies in `End^n(𝓛)` exactly when `n ≤ e(𝓛)`. -/
theorem algebraMap_uniformizer_mem_endFiltration_iff (𝓛 : LatticeChain 𝒪[F] F V)
    {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) (n : ℤ) :
    algebraMap F (Module.End F V) (ϖ : F) ∈ 𝓛.endFiltration n ↔ n ≤ 𝓛.period := by
  rw [mem_endFiltration]
  simp only [Module.algebraMap_end_apply]
  constructor
  · intro h
    obtain ⟨v, hv, hv1⟩ := IsConcreteLE.exists_of_lt (𝓛.lattice_succ_lt 0)
    have h1 := h 0 v (by simpa using hv)
    rw [𝓛.uniformizer_smul_mem_iff hϖ] at h1
    by_contra hlt
    exact hv1 (𝓛.antitone (by simp; omega) h1)
  · intro hn i v hv
    rw [𝓛.uniformizer_smul_mem_iff hϖ]
    exact 𝓛.antitone (by omega) hv

/-- Two lattice chains with the same hereditary order have the same period. -/
theorem period_eq_of_order_eq {L M : LatticeChain 𝒪[F] F V} (h : L.order = M.order) :
    L.period = M.period := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  have hE := endFiltration_eq_of_order_eq h
  have key : ∀ n : ℤ, n ≤ L.period ↔ n ≤ M.period := fun n => by
    rw [← L.algebraMap_uniformizer_mem_endFiltration_iff hϖ,
      ← M.algebraMap_uniformizer_mem_endFiltration_iff hϖ, hE]
  have h1 := (key L.period).1 le_rfl
  have h2 := (key M.period).2 le_rfl
  exact_mod_cast le_antisymm h1 h2

/-! ### The period divides the dimension -/

/-- The period of a principal lattice chain divides `N = dim_F V`. -/
theorem period_dvd_finrank_of_isPrincipal [FiniteDimensional F V] (𝓛 : LatticeChain 𝒪[F] F V)
    (hP : 𝓛.IsPrincipal) : 𝓛.period ∣ Module.finrank F V := by
  set q := Nat.card (ResidueField 𝒪[F]) with hqdef
  have hq : 1 < q := Finite.one_lt_card
  have h1 : ((𝓛.lattice 1).toAddSubgroup.relIndex (𝓛.lattice 0).toAddSubgroup) ^ 𝓛.period =
      q ^ Module.finrank F V := by
    rw [← 𝓛.relIndex_lattice_natCast_of_isPrincipal hP, ← natCard_interval_eq_relIndex,
      natCard_interval_period]
  have hc : Nat.card (𝓛.Layer 0) =
      (𝓛.lattice 1).toAddSubgroup.relIndex (𝓛.lattice 0).toAddSubgroup :=
    𝓛.natCard_interval_eq_relIndex 0 (0 + 1)
  have : Module.Finite 𝒪[F] (𝓛.lattice 0) := Module.Finite.iff_fg.mpr (𝓛.fg_lattice 0)
  have : Module.Finite (ResidueField 𝒪[F]) (𝓛.Layer 0) :=
    Module.Finite.of_restrictScalars_finite 𝒪[F] _ _
  have : Finite (𝓛.Layer 0) := Module.finite_of_finite (ResidueField 𝒪[F])
  have h2 : Nat.card (𝓛.Layer 0) =
      q ^ Module.finrank (ResidueField 𝒪[F]) (𝓛.Layer 0) := Module.natCard_eq_pow_finrank
  rw [← hc, h2, ← pow_mul] at h1
  exact ⟨_, (Nat.pow_right_injective hq h1).symm.trans (mul_comm _ _)⟩

/-- The period of a lattice chain whose order is principal divides `N = dim_F V`. -/
theorem period_dvd_finrank_of_isPrincipalOrder [FiniteDimensional F V]
    (𝓛 : LatticeChain 𝒪[F] F V) (h : IsPrincipalOrder 𝓛.order) :
    𝓛.period ∣ Module.finrank F V := by
  obtain ⟨M, hM, hP⟩ := h
  rw [period_eq_of_order_eq hM.symm]
  exact M.period_dvd_finrank_of_isPrincipal hP

/-! ### Splitting bases with indices in one period -/

section Splitting

variable {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- For a basis splitting `𝓛`, a vector lies in `L_i` exactly when all its basis terms do. -/
theorem mem_lattice_iff_of_splits (𝓛 : LatticeChain 𝒪[F] F V) {κ : Type*} [Fintype κ]
    (β : Module.Basis κ F V) (hβ : 𝓛.Splits β) (i : ℤ) (v : V) :
    v ∈ 𝓛.lattice i ↔ ∀ k, β.repr v k • β k ∈ 𝓛.lattice i := by
  constructor
  · intro hv
    exact hβ (fun k => β.repr v k) i (by rw [β.sum_repr v]; exact hv)
  · intro h
    rw [← β.sum_repr v]
    exact sum_mem fun k _ => h k

/-- For `x ≠ 0`, `c • x ∈ L_j` holds exactly when `c = 0` or `j ≤ ν(x) + e ord(c)`. -/
theorem smul_mem_lattice_iff_index (𝓛 : LatticeChain 𝒪[F] F V) {x : V} (hx : x ≠ 0) (c : F)
    (j : ℤ) : c • x ∈ 𝓛.lattice j ↔ c = 0 ∨ j ≤ 𝓛.index hϖ x + 𝓛.period * ordOf hϖ c := by
  by_cases hc : c = 0
  · simp [hc]
  · rw [𝓛.mem_iff_le_index hϖ (smul_ne_zero hc hx), 𝓛.index_smul hϖ hc hx]
    simp [hc]

/-- A nonzero integral element has zero residue exactly when its order is at least one. -/
theorem residue_eq_zero_iff_one_le_ordOf {c : F} (hc0 : c ≠ 0) (hc : c ∈ 𝒪[F]) :
    residue 𝒪[F] ⟨c, hc⟩ = 0 ↔ 1 ≤ ordOf hϖ c := by
  rw [residue_eq_zero_iff, hϖ.maximalIdeal_eq, Ideal.mem_span_singleton']
  have hϖ0 : (ϖ : F) ≠ 0 := coe_uniformizer_ne_zero hϖ
  have hord : ordOf hϖ (ϖ : F) = 1 := by simpa using ordOf_zpow hϖ 1
  constructor
  · rintro ⟨a, ha⟩
    have ha' : (a : F) * (ϖ : F) = c := congrArg Subtype.val ha
    have ha0 : (a : F) ≠ 0 := by
      intro h
      rw [h, zero_mul] at ha'
      exact hc0 ha'.symm
    rw [← ha', ordOf_mul hϖ ha0 hϖ0, hord]
    have := ordOf_nonneg hϖ ha0 a.2
    omega
  · intro h
    have hd0 : (ϖ : F)⁻¹ * c ≠ 0 := mul_ne_zero (inv_ne_zero hϖ0) hc0
    have hd : (ϖ : F)⁻¹ * c ∈ 𝒪[F] := by
      apply mem_integer_of_ordOf_nonneg hϖ hd0
      rw [ordOf_mul hϖ (inv_ne_zero hϖ0) hc0, ordOf_inv hϖ hϖ0, hord]
      omega
    refine ⟨⟨_, hd⟩, Subtype.ext ?_⟩
    change (ϖ : F)⁻¹ * c * (ϖ : F) = c
    field_simp

/-- Every lattice chain has a splitting basis whose vectors have indices in `[0, e)`. -/
theorem exists_basis_splits_index_lt (𝓛 : LatticeChain 𝒪[F] F V) :
    ∃ (r : ℕ) (β : Module.Basis (Fin r) F V), 𝓛.Splits β ∧
      ∀ k, 0 ≤ 𝓛.index hϖ (β k) ∧ 𝓛.index hϖ (β k) < 𝓛.period := by
  obtain ⟨r, β, hβ⟩ := exists_basis_splits hϖ 𝓛
  have he : (0 : ℤ) < 𝓛.period := by exact_mod_cast 𝓛.period_pos
  let t : Fin r → ℤ := fun k => 𝓛.index hϖ (β k) / 𝓛.period
  let w : Fin r → Fˣ := fun k => (uniformizerAsUnit hϖ) ^ (-t k)
  refine ⟨r, β.unitsSMul w, ?_, fun k => ?_⟩
  · intro c i hc k
    have hc' : ∑ k, (c k * (w k : F)) • β k ∈ 𝓛.lattice i := by
      simpa [Module.Basis.unitsSMul_apply, Units.smul_def, smul_smul] using hc
    have := hβ (fun k => c k * (w k : F)) i hc' k
    simpa [Module.Basis.unitsSMul_apply, Units.smul_def, smul_smul] using this
  · have hw : ((w k : Fˣ) : F) = (ϖ : F) ^ (-t k) := by simp [w]
    have hwne : ((w k : Fˣ) : F) ≠ 0 := Units.ne_zero _
    have hidx : 𝓛.index hϖ ((β.unitsSMul w) k) = 𝓛.index hϖ (β k) % 𝓛.period := by
      rw [Module.Basis.unitsSMul_apply, Units.smul_def, 𝓛.index_smul hϖ hwne (β.ne_zero k), hw,
        ordOf_zpow, Int.emod_def]
      ring
    rw [hidx]
    exact ⟨Int.emod_nonneg _ he.ne', Int.emod_lt_of_pos _ he⟩

/-- For a basis splitting `𝓛` with indices in `[0, e)` and `0 ≤ s < e`, the layer
`L_s / L_{s+1}` has `q^{n_s}` elements, where `n_s` is the number of basis vectors of
index `s`. -/
theorem natCard_layer_of_splits (𝓛 : LatticeChain 𝒪[F] F V) {r : ℕ}
    (β : Module.Basis (Fin r) F V) (hβ : 𝓛.Splits β)
    (hidx : ∀ k, 0 ≤ 𝓛.index hϖ (β k) ∧ 𝓛.index hϖ (β k) < 𝓛.period)
    {s : ℤ} (hs0 : 0 ≤ s) (hse : s < 𝓛.period) :
    Nat.card (𝓛.Layer s) =
      Nat.card (ResidueField 𝒪[F]) ^ Fintype.card {k // 𝓛.index hϖ (β k) = s} := by
  classical
  have he : (0 : ℤ) < 𝓛.period := by exact_mod_cast 𝓛.period_pos
  have hcoeff : ∀ v ∈ 𝓛.lattice s, ∀ k : {k // 𝓛.index hϖ (β k) = s}, β.repr v k ∈ 𝒪[F] := by
    intro v hv k
    by_cases hc : β.repr v k = 0
    · rw [hc]
      exact zero_mem _
    have h := (mem_lattice_iff_of_splits 𝓛 β hβ s v).1 hv k
    rw [𝓛.smul_mem_lattice_iff_index hϖ (β.ne_zero k), k.2] at h
    rcases h with h | h
    · exact absurd h hc
    · apply mem_integer_of_ordOf_nonneg hϖ hc
      by_contra hneg
      nlinarith [not_le.mp hneg]
  let ψ : 𝓛.lattice s →ₗ[𝒪[F]] ({k // 𝓛.index hϖ (β k) = s} → ResidueField 𝒪[F]) :=
    { toFun := fun v k => residue 𝒪[F] ⟨β.repr v k, hcoeff v v.2 k⟩
      map_add' := by
        intro v w
        funext k
        rw [Pi.add_apply, ← map_add]
        congr 1
        apply Subtype.ext
        simp
      map_smul' := by
        intro a v
        funext k
        rw [RingHom.id_apply, Pi.smul_apply, Algebra.smul_def, ResidueField.algebraMap_eq,
          ← map_mul]
        congr 1
        apply Subtype.ext
        change β.repr ((a : F) • (v : V)) k = (a : F) * β.repr v k
        simp }
  have hψ : ∀ v : 𝓛.lattice s,
      ψ v = fun k : {k // 𝓛.index hϖ (β k) = s} => residue 𝒪[F] ⟨β.repr v k, hcoeff v v.2 k⟩ :=
    fun _ => rfl
  have hker : ∀ v : 𝓛.lattice s, ψ v = 0 ↔ (v : V) ∈ 𝓛.lattice (s + 1) := by
    intro v
    rw [mem_lattice_iff_of_splits 𝓛 β hβ (s + 1)]
    have hv := (mem_lattice_iff_of_splits 𝓛 β hβ s v).1 v.2
    rw [hψ, funext_iff]
    constructor
    · intro h0 k
      have hk := hv k
      rw [𝓛.smul_mem_lattice_iff_index hϖ (β.ne_zero k)] at hk ⊢
      by_cases hc : β.repr v k = 0
      · exact Or.inl hc
      right
      by_cases hks : 𝓛.index hϖ (β k) = s
      · have h1 := h0 ⟨k, hks⟩
        rw [Pi.zero_apply, residue_eq_zero_iff_one_le_ordOf hϖ hc] at h1
        rw [hks]
        nlinarith
      · rcases hk with hk | hk
        · exact absurd hk hc
        obtain ⟨hi0, hie⟩ := hidx k
        rcases lt_trichotomy (ordOf hϖ (β.repr v k)) 0 with ho | ho | ho
        · nlinarith
        · rw [ho, mul_zero, add_zero] at hk ⊢
          omega
        · nlinarith
    · intro h1 k
      rw [Pi.zero_apply]
      by_cases hc : β.repr v k = 0
      · have : (⟨β.repr v k, hcoeff v v.2 k⟩ : 𝒪[F]) = 0 := Subtype.ext hc
        rw [this, map_zero]
      rw [residue_eq_zero_iff_one_le_ordOf hϖ hc]
      have hk := h1 k
      rw [𝓛.smul_mem_lattice_iff_index hϖ (β.ne_zero k), k.2] at hk
      rcases hk with hk | hk
      · exact absurd hk hc
      · nlinarith
  have hsurj : Function.Surjective ψ := by
    intro y
    choose a ha using fun k : {k // 𝓛.index hϖ (β k) = s} => residue_surjective (y k)
    let c : Fin r → F := fun k => if h : 𝓛.index hϖ (β k) = s then ((a ⟨k, h⟩ : 𝒪[F]) : F) else 0
    let v := β.equivFun.symm c
    have hrepr : ∀ k, β.repr v k = c k := fun k => by
      rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
    have hv : v ∈ 𝓛.lattice s := by
      rw [mem_lattice_iff_of_splits 𝓛 β hβ s]
      intro k
      rw [hrepr]
      by_cases hk : 𝓛.index hϖ (β k) = s
      · simp only [c, hk, ↓reduceDIte]
        have hmem : β k ∈ 𝓛.lattice s := hk ▸ 𝓛.mem_lattice_index hϖ (β.ne_zero k)
        exact (𝓛.lattice s).smul_mem (a ⟨k, hk⟩) hmem
      · simp only [c, hk, ↓reduceDIte, zero_smul]
        exact zero_mem _
    refine ⟨⟨v, hv⟩, funext fun k => ?_⟩
    rw [hψ, ← ha k]
    dsimp only
    congr 1
    apply Subtype.ext
    change β.repr v k = _
    rw [hrepr]
    simp [c, k.2]
  have hkerEq : 𝓛.intervalSubmodule s (s + 1) = LinearMap.ker ψ := by
    ext v
    rw [LinearMap.mem_ker, hker]
    rfl
  calc Nat.card (𝓛.Layer s)
      = Nat.card ((𝓛.lattice s) ⧸ LinearMap.ker ψ) :=
        Nat.card_congr (Submodule.quotEquivOfEq _ _ hkerEq).toEquiv
    _ = Nat.card ({k // 𝓛.index hϖ (β k) = s} → ResidueField 𝒪[F]) :=
        Nat.card_congr (ψ.quotKerEquivOfSurjective hsurj).toEquiv
    _ = _ := by
        rw [Nat.card_fun]
        congr 1
        exact Nat.card_eq_fintype_card

/-- In a splitting basis of a principal chain with indices in `[0, e)`, every index in
`[0, e)` is taken by `N / e` basis vectors. -/
theorem card_index_eq_of_isPrincipal [FiniteDimensional F V] (𝓛 : LatticeChain 𝒪[F] F V)
    (hP : 𝓛.IsPrincipal) {r : ℕ} (β : Module.Basis (Fin r) F V) (hβ : 𝓛.Splits β)
    (hidx : ∀ k, 0 ≤ 𝓛.index hϖ (β k) ∧ 𝓛.index hϖ (β k) < 𝓛.period)
    {s : ℤ} (hs0 : 0 ≤ s) (hse : s < 𝓛.period) :
    Fintype.card {k // 𝓛.index hϖ (β k) = s} * 𝓛.period = Module.finrank F V := by
  classical
  have hq : 1 < Nat.card (ResidueField 𝒪[F]) := Finite.one_lt_card
  have he : (0 : ℤ) < 𝓛.period := by exact_mod_cast 𝓛.period_pos
  have hall : ∀ t : ℤ, 0 ≤ t → t < 𝓛.period →
      Fintype.card {k // 𝓛.index hϖ (β k) = t} = Fintype.card {k // 𝓛.index hϖ (β k) = s} := by
    intro t ht0 hte
    have h := hP t s
    rw [← natCard_interval_eq_relIndex, ← natCard_interval_eq_relIndex,
      𝓛.natCard_layer_of_splits hϖ β hβ hidx ht0 hte,
      𝓛.natCard_layer_of_splits hϖ β hβ hidx hs0 hse] at h
    exact Nat.pow_right_injective hq h
  have hsum : (Finset.univ : Finset (Fin r)).card =
      ∑ t ∈ Finset.Ico (0 : ℤ) 𝓛.period,
        (Finset.univ.filter fun k => 𝓛.index hϖ (β k) = t).card := by
    apply Finset.card_eq_sum_card_fiberwise
    intro k _
    simpa using hidx k
  rw [Module.finrank_eq_card_basis β, ← Finset.card_univ (α := Fin r)]
  rw [hsum, Finset.sum_congr rfl (g := fun _ => Fintype.card {k // 𝓛.index hϖ (β k) = s}),
    Finset.sum_const, Int.card_Ico, smul_eq_mul, sub_zero, Int.toNat_natCast, mul_comm]
  intro t ht
  rw [Finset.mem_Ico] at ht
  rw [← hall t ht.1 ht.2, Fintype.card_subtype]

/-- Two principal lattice chains of the same period in `V` correspond under a linear
automorphism of `V`. -/
theorem exists_linearEquiv_corresponds_of_isPrincipal [FiniteDimensional F V]
    {𝓛 𝓜 : LatticeChain 𝒪[F] F V} (h𝓛 : 𝓛.IsPrincipal) (h𝓜 : 𝓜.IsPrincipal)
    (he : 𝓛.period = 𝓜.period) :
    ∃ f : V ≃ₗ[F] V, 𝓛.Corresponds f 𝓜 := by
  classical
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  obtain ⟨r, β, hβ, hidx⟩ := 𝓛.exists_basis_splits_index_lt hϖ
  obtain ⟨r', γ, hγ, hidx'⟩ := 𝓜.exists_basis_splits_index_lt hϖ
  have he0 : (0 : ℤ) < 𝓛.period := by exact_mod_cast 𝓛.period_pos
  have hcard : ∀ s : ℤ, Fintype.card {k // 𝓛.index hϖ (β k) = s} =
      Fintype.card {k // 𝓜.index hϖ (γ k) = s} := by
    intro s
    by_cases hs : 0 ≤ s ∧ s < 𝓛.period
    · have h1 := 𝓛.card_index_eq_of_isPrincipal hϖ h𝓛 β hβ hidx hs.1 hs.2
      have h2 := 𝓜.card_index_eq_of_isPrincipal hϖ h𝓜 γ hγ hidx' hs.1 (he ▸ hs.2)
      rw [← he, ← h1] at h2
      exact (Nat.eq_of_mul_eq_mul_right 𝓛.period_pos h2).symm
    · have h1 : IsEmpty {k // 𝓛.index hϖ (β k) = s} :=
        ⟨fun k => hs ⟨k.2 ▸ (hidx k).1, k.2 ▸ (hidx k).2⟩⟩
      have h2 : IsEmpty {k // 𝓜.index hϖ (γ k) = s} :=
        ⟨fun k => hs ⟨k.2 ▸ (hidx' k).1, he ▸ k.2 ▸ (hidx' k).2⟩⟩
      rw [Fintype.card_eq_zero, Fintype.card_eq_zero]
  obtain ⟨π, hπ⟩ : ∃ π : Fin r ≃ Fin r', ∀ k, 𝓜.index hϖ (γ (π k)) = 𝓛.index hϖ (β k) :=
    ⟨Equiv.ofFiberEquiv fun s => Fintype.equivOfCardEq (hcard s),
      Equiv.ofFiberEquiv_map (f := fun k => 𝓛.index hϖ (β k))
        (g := fun k => 𝓜.index hϖ (γ k)) _⟩
  obtain ⟨f, hfb⟩ : ∃ f : V ≃ₗ[F] V, ∀ k, f (β k) = γ (π k) :=
    ⟨β.equiv γ π, fun k => by simp⟩
  have hterm : ∀ (i : ℤ) (k : Fin r) (c : F), c • β k ∈ 𝓛.lattice i ↔ c • γ (π k) ∈ 𝓜.lattice i := by
    intro i k c
    rw [𝓛.smul_mem_lattice_iff_index hϖ (β.ne_zero k), 𝓜.smul_mem_lattice_iff_index hϖ
      (γ.ne_zero _), hπ, he]
  have hf : ∀ v : V, f v = ∑ k, β.repr v k • γ (π k) := by
    intro v
    calc f v = f (∑ k, β.repr v k • β k) := by rw [β.sum_repr]
      _ = ∑ k, β.repr v k • γ (π k) := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [map_smul, hfb]
  refine ⟨f, fun i v => ?_⟩
  rw [mem_lattice_iff_of_splits 𝓛 β hβ i, hf]
  constructor
  · intro h
    exact sum_mem fun k _ => (hterm i k _).1 (h k)
  · intro h k
    rw [hterm]
    have h' : ∑ k', β.repr v (π.symm k') • γ k' ∈ 𝓜.lattice i := by
      rw [← Equiv.sum_comp π]
      simpa using h
    simpa using hγ (fun k' => β.repr v (π.symm k')) i h' (π k)

end Splitting

/-- Two lattice chains whose orders are principal of the same period have conjugate orders
(BK93 §1.1, printed pp. 22–23). -/
theorem exists_order_eq_of_isPrincipalOrder [FiniteDimensional F V]
    (L₁ L₂ : LatticeChain 𝒪[F] F V) (h₁ : IsPrincipalOrder L₁.order)
    (h₂ : IsPrincipalOrder L₂.order) (he : L₁.period = L₂.period) :
    ∃ g : (Module.End F V)ˣ,
      (L₁.linearEquivMap (LinearMap.GeneralLinearGroup.toLinearEquiv g)).order = L₂.order := by
  obtain ⟨M₁, hM₁, hP₁⟩ := h₁
  obtain ⟨M₂, hM₂, hP₂⟩ := h₂
  have he' : M₁.period = M₂.period := by
    rw [period_eq_of_order_eq hM₁, period_eq_of_order_eq hM₂, he]
  obtain ⟨f, hf⟩ := exists_linearEquiv_corresponds_of_isPrincipal hP₁ hP₂ he'
  refine ⟨LinearMap.GeneralLinearGroup.ofLinearEquiv f, ?_⟩
  have hfg : LinearMap.GeneralLinearGroup.toLinearEquiv
      (LinearMap.GeneralLinearGroup.ofLinearEquiv f) = f := LinearEquiv.ext fun _ => rfl
  rw [hfg, ← hM₂]
  have hL : L₁.Corresponds f (L₁.linearEquivMap f) := by
    intro i v
    rw [mem_linearEquivMap, LinearEquiv.symm_apply_apply]
  exact (hL.order_eq_iff hf).2 hM₁.symm

end Langlands.BushnellKutzko.LatticeChain
