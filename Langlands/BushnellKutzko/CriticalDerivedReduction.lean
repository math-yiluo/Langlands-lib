import Langlands.BushnellKutzko.CriticalDerivedScalars

/-! # Scalar symbols for the actual generated fields of two strata -/

noncomputable section

open ValuativeRel

namespace Langlands.BushnellKutzko.CriticalDerived

open StratumEquivalence

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] (𝓛 : LatticeChain 𝒪[F] F V)

local notation "P" => 𝓛.endFiltration
local notation "[" x "," y "]ₐ" => x * y - y * x

section

variable (β γ : Module.End F V) (d : ℤ)
  (hβfield : IsField (elementAlgebra β)) (hγfield : IsField (elementAlgebra γ))

local notation "E" => elementAlgebra γ
local notation "K" => elementAlgebra β
local notation "b" => (β - γ)
local notation "ιE" => subfieldEmbedding F E V
local notation "ιK" => subfieldEmbedding F K V

/-- At the critical level the derived element has a nonzero scalar symbol from `F[β]`.
    The scalar symbols from `F[γ]` also lie in those from `F[β]` in every degree. -/
theorem derived_scalar_symbols (hb : b ∈ P d)
    (hkβ : criticalExponent 𝓛 β = (d : WithBot ℤ))
    (hkγ : criticalExponent 𝓛 γ < (d : WithBot ℤ)) :
    letI := hγfield.toField
    letI := hβfield.toField
    ∀ (s : TameCorestriction 𝒪[F] F E V)
      (_hE : ∀ u : Eˣ, subfieldUnits F E V u ∈ 𝓛.stabilizer)
      (_hK : ∀ u : Kˣ, subfieldUnits F K V u ∈ 𝓛.stabilizer),
      let a := ambientCorestriction s b
      (a ∈ P d ∧ a ∉ P (d + 1) ∧ ∃ c : K, ιK c ∈ P d ∧ a - ιK c ∈ P (d + 1)) ∧
        ∀ (j : ℤ) (e : E), ιE e ∈ P j → ∃ c : K, ιK c ∈ P j ∧ ιE e - ιK c ∈ P (j + 1) := by
  let := hγfield.toField
  let := hβfield.toField
  intro s hE hK
  let t := ambientCorestriction s
  let a := t b
  have hγ0 := subfieldEmbedding_elementGenerator γ hγfield
  have hβ0 := subfieldEmbedding_elementGenerator β hβfield
  have hβγ : β = γ + b := by abel
  have hkγ' := withBot_le_sub_one_of_lt hkγ
  have hγ (j : ℤ) (x : Module.End F V) (hx : [γ, x]ₐ ∈ P (d + j)) :
      ∃ y, Commute y γ ∧ x - y ∈ P (j + 1) := by
    rw [show d + j = j + 1 + (d - 1) by omega] at hx
    obtain ⟨y, hy, hxy⟩ := exists_commute_sub_mem 𝓛 γ hγfield hE hkγ' (j + 1) x hx
    exact ⟨y, (sub_eq_zero.mp hy).symm, hxy⟩
  have hβ (j : ℤ) (x : Module.End F V) (hx : [β, x]ₐ ∈ P (d + j + 1)) :
      ∃ y, Commute y β ∧ x - y ∈ P (j + 1) := by
    rw [show d + j + 1 = j + 1 + d by omega] at hx
    obtain ⟨y, hy, hxy⟩ := exists_commute_sub_mem 𝓛 β hβfield hK hkβ.le (j + 1) x hx
    exact ⟨y, (sub_eq_zero.mp hy).symm, hxy⟩
  have hs_mem {n : ℤ} {x : Module.End F V} (hx : x ∈ P n) : t x ∈ P n :=
    ambientCorestriction_mem 𝓛 s hE hx
  have hs_adj (x : Module.End F V) : t [γ, x]ₐ = 0 :=
    hγ0 ▸ ambientCorestriction_adjoint s (γE := elementGenerator γ) x
  have hs_comm (x y : Module.End F V) (hy : Commute y γ) : t [x, y]ₐ = [t x, y]ₐ :=
    ambientCorestriction_commutator s (adjoin_elementGenerator γ) (hγ0.symm ▸ hy)
  have hs_corr (j : ℤ) (x : Module.End F V) (hx : x ∈ P (d + j)) (hsx : t x ∈ P (d + j + 1)) :
      ∃ u ∈ P (j + 1), x - [γ, u]ₐ ∈ P (d + j + 1) := by
    rw [← hγ0]
    exact exists_adjoint_correction 𝓛 s hE (adjoin_elementGenerator γ) d j
      (hγ0.symm ▸ hkγ') hx hsx
  have hf (i : ℤ) (x : Module.End F V) (hx : x ∈ P i) (hxc : Commute x β) :
      ∃ y ∈ P i, Commute y γ ∧ x - y ∈ P (i + 1) ∧ [a, y]ₐ ∈ P (d + i + 1) :=
    approx_original_centralizer 𝓛 hb hβγ t rfl @hs_mem hs_adj hs_comm hγ hx hxc
  have hbw {i : ℤ} {x : Module.End F V} (hx : x ∈ P i) (hxc : Commute x γ)
      (hxa : [a, x]ₐ ∈ P (d + i + 1)) : ∃ y ∈ P i, Commute y β ∧ x - y ∈ P (i + 1) :=
    approx_perturbed_centralizer 𝓛 hb hβγ t rfl hs_comm hs_corr hβ hx hxc hxa
  have hd : d ∈ criticalIndexSet 𝓛 β := by
    have hbot : elementAlgebra β ≠ ⊥ := by
      intro h
      simp [criticalExponent, h] at hkβ
    obtain ⟨k, hk, hek⟩ := exists_isGreatest_criticalIndexSet 𝓛 β hβfield hK hbot
    rw [show d = k from WithBot.coe_injective (hkβ.symm.trans hek)]
    exact hk.1
  have ha := hs_mem hb
  have ha' := not_mem_succ_of_critical 𝓛 hb hd (a := a)
    (fun x hx => by simpa only [add_zero, zero_add] using hγ 0 x (by simpa only [add_zero] using hx))
    (fun x hx hxc hxa => by
      simpa only [add_zero, zero_add] using hbw hx hxc (by simpa only [add_zero] using hxa))
  have commβ {x : Module.End F V} (hx : x ∈ fieldCommutant K) : Commute x β := by
    rw [← hβ0]
    ext v
    exact hx (elementGenerator β) v
  refine ⟨⟨ha, ha', exists_scalar_of_graded_commutation 𝓛 hK ha ?_⟩, ?_⟩
  · intro i x hx hxc
    exact graded_commutation_of_approx 𝓛 @hf ha (fun _ _ _ h => h) i hx (commβ hxc)
  · intro j e he
    apply exists_scalar_of_graded_commutation 𝓛 hK he
    intro i x hx hxc
    apply graded_commutation_of_approx 𝓛 @hf he _ i hx (commβ hxc)
    intro i y hy _
    obtain ⟨Y, rfl⟩ := exists_restrictScalars_of_commute (adjoin_elementGenerator γ) (hγ0.symm ▸ hy)
    rw [(restrictScalars_commute Y e).eq, sub_self]
    exact zero_mem _

end

end Langlands.BushnellKutzko.CriticalDerived
