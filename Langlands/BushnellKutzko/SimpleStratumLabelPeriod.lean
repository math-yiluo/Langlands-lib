import Langlands.BushnellKutzko.UnitFiltration
import Langlands.BushnellKutzko.LatticeChain

/-! # The period of a principal lattice chain divides the dimension -/

open ValuativeRel

noncomputable section

namespace Langlands.BushnellKutzko.SimpleStratumLabel

universe uK uV

variable {K : Type uK} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {V : Type uV} [AddCommGroup V] [Module K V]

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem relIndex_eq_natCard_quotient (N₀ N₁ : Submodule 𝒪[K] V) :
    N₁.toAddSubgroup.relIndex N₀.toAddSubgroup = Nat.card (N₀ ⧸ N₁.comap N₀.subtype) :=
  rfl

/-- If `𝔭 N₀ ⊆ N₁ ⊆ N₀` with `N₀` finitely generated, then `(N₀ : N₁)` is a power of `q`. -/
theorem exists_relIndex_eq_pow (N₀ N₁ : Submodule 𝒪[K] V) (hfg : N₀.FG)
    (h𝔪 : 𝓂[K] • N₀ ≤ N₁) :
    ∃ a : ℕ, N₁.toAddSubgroup.relIndex N₀.toAddSubgroup = Nat.card 𝓀[K] ^ a := by
  rw [relIndex_eq_natCard_quotient]
  set A := N₁.comap N₀.subtype
  have hT : Module.IsTorsionBySet 𝒪[K] (N₀ ⧸ A) (𝓂[K] : Set 𝒪[K]) := by
    intro x a
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective A x
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    change ((a : 𝒪[K]) • (y : V)) ∈ N₁
    exact h𝔪 (Submodule.smul_mem_smul a.2 y.2)
  let : Module (𝒪[K] ⧸ 𝓂[K]) (N₀ ⧸ A) := hT.module
  have : IsScalarTower 𝒪[K] (𝒪[K] ⧸ 𝓂[K]) (N₀ ⧸ A) := hT.isScalarTower
  have : Module.Finite 𝒪[K] N₀ := Module.Finite.iff_fg.mpr hfg
  have : Module.Finite (𝒪[K] ⧸ 𝓂[K]) (N₀ ⧸ A) :=
    Module.Finite.of_restrictScalars_finite 𝒪[K] _ _
  have : Finite (𝒪[K] ⧸ 𝓂[K]) := inferInstanceAs (Finite 𝓀[K])
  let : Field (𝒪[K] ⧸ 𝓂[K]) := Ideal.Quotient.field _
  refine ⟨Module.finrank (𝒪[K] ⧸ 𝓂[K]) (N₀ ⧸ A), ?_⟩
  rw [Module.natCard_eq_pow_finrank (K := 𝒪[K] ⧸ 𝓂[K])]
  rfl


/-- For a lattice `N₀`, the index `(N₀ : 𝔭 N₀)` is `q^{dim V}`. -/
theorem relIndex_maximalIdeal_smul [FiniteDimensional K V] (N₀ : Submodule 𝒪[K] V)
    (hN : N₀.IsLattice K) :
    (𝓂[K] • N₀).toAddSubgroup.relIndex N₀.toAddSubgroup =
      Nat.card 𝓀[K] ^ Module.finrank K V := by
  rw [relIndex_eq_natCard_quotient]
  have hA : (𝓂[K] • N₀).comap N₀.subtype = 𝓂[K] • (⊤ : Submodule 𝒪[K] N₀) := by
    apply Submodule.map_injective_of_injective N₀.injective_subtype
    simp only [Submodule.map_comap_subtype, Submodule.map_smul'', Submodule.map_subtype_top]
    exact inf_eq_right.2 Submodule.smul_le_right
  rw [hA]
  have hfg : N₀.FG := hN.fg
  have : Module.Finite 𝒪[K] N₀ := Module.Finite.iff_fg.mpr hfg
  let : Field (𝒪[K] ⧸ 𝓂[K]) := Ideal.Quotient.field _
  have : Module.Finite (𝒪[K] ⧸ 𝓂[K]) (N₀ ⧸ 𝓂[K] • (⊤ : Submodule 𝒪[K] N₀)) :=
    Module.Finite.of_restrictScalars_finite 𝒪[K] _ _
  have hrank : Module.finrank 𝒪[K] N₀ = Module.finrank K V := by
    unfold Module.finrank
    rw [Submodule.IsLattice.rank' K N₀]
  rw [Module.natCard_eq_pow_finrank (K := 𝒪[K] ⧸ 𝓂[K]),
    ← IsLocalRing.spanFinrank_eq_finrank_quotient N₀ hfg, ← Submodule.spanFinrank_top,
    ← Module.finrank_eq_spanFinrank_of_free, hrank]
  rfl

/-- The period of a principal lattice chain divides the dimension: a principal chain
has `e` layers of the same dimension `d` over the residue field, with `e d = N`. -/
theorem period_dvd_finrank_of_isPrincipal [FiniteDimensional K V]
    (L : LatticeChain 𝒪[K] K V) (hP : L.IsPrincipal) :
    L.period ∣ Module.finrank K V := by
  set c := (L.lattice 1).toAddSubgroup.relIndex (L.lattice 0).toAddSubgroup with hc
  have hstep (j : ℤ) : (L.lattice (j + 1)).toAddSubgroup.relIndex (L.lattice j).toAddSubgroup =
      c := by
    rw [hc, hP j 0, zero_add]
  have hpow (k : ℕ) : (L.lattice k).toAddSubgroup.relIndex (L.lattice 0).toAddSubgroup =
      c ^ k := by
    induction k with
    | zero => simp
    | succ k ih =>
      have hle1 : (L.lattice ((k + 1 : ℕ) : ℤ)).toAddSubgroup ≤ (L.lattice k).toAddSubgroup :=
        L.antitone (by omega)
      have hle2 : (L.lattice (k : ℤ)).toAddSubgroup ≤ (L.lattice 0).toAddSubgroup :=
        L.antitone (by omega)
      rw [← AddSubgroup.relIndex_mul_relIndex _ _ _ hle1 hle2, ih, pow_succ, mul_comm]
      congr 1
      have := hstep k
      push_cast at this ⊢
      exact this
  have hLe : L.lattice (L.period : ℕ) = 𝓂[K] • L.lattice 0 := by
    have h := L.lattice_add_period 0
    rw [zero_add, jacobson_integer_eq_maximalIdeal] at h
    exact h
  have h1 := hpow L.period
  rw [hLe, relIndex_maximalIdeal_smul (L.lattice 0) (L.isLattice 0)] at h1
  obtain ⟨a, ha⟩ := exists_relIndex_eq_pow (L.lattice 0) (L.lattice 1) (L.fg_lattice 0) (by
    rw [← hLe]
    exact L.antitone (by have := L.period_pos; omega))
  rw [← hc] at ha
  rw [ha, ← pow_mul] at h1
  have hq : 1 < Nat.card 𝓀[K] := Finite.one_lt_card
  have := Nat.pow_right_injective hq h1
  exact ⟨a, by rw [this, mul_comm]⟩

end Langlands.BushnellKutzko.SimpleStratumLabel
