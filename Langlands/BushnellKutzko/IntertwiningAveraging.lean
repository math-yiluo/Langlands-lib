import Mathlib.Analysis.Complex.Basic
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RepresentationTheory.Subrepresentation
import Mathlib.GroupTheory.Index
import Mathlib.Topology.Algebra.OpenSubgroup
import Langlands.Representation.FiniteVectors

/-! # Intertwining of a character and a fixed vector by finite averaging

Let `ρ` be an irreducible complex representation of a group `G`, let `H, J` be subgroups of
`G`, and let `χ : G → ℂ`. Suppose that some nonzero vector `v` satisfies `ρ(h) v = χ(h) v` for
`h ∈ H`, that `χ` is trivial on a subgroup of finite index of `H`, and that some nonzero
vector `w` is fixed by `J`. If every subgroup `H ∩ g J g⁻¹` has finite index in `H`, then
`χ` is trivial on `H ∩ g J g⁻¹` for some `g ∈ G` (`exists_forall_conj_mem_eq_one`).

The proof writes `v` as a finite combination `∑ c_g ρ(g) w` (irreducibility) and applies the
operator `∑_{q ∈ H/S} χ(q)⁻¹ ρ(q)` for a normal subgroup `S` of finite index in `H` that fixes
`v` and every `ρ(g) w`: it multiplies `v` by `[H : S]` and kills every `ρ(g) w` for which
`χ` is nontrivial on `H ∩ g J g⁻¹`.

`relIndex_ne_zero_of_isCompact`: an open subgroup has finite index in a compact subgroup.
-/

noncomputable section

namespace Langlands.BushnellKutzko

section Averaging

variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- In an irreducible representation, every vector is a finite linear combination of
translates of a given nonzero vector. -/
theorem exists_finsupp_sum_eq (ρ : Representation ℂ G V) [ρ.IsIrreducible] {w : V}
    (hw : w ≠ 0) (v : V) : ∃ c : G →₀ ℂ, (c.sum fun g a => a • ρ g w) = v := by
  rw [← Finsupp.mem_span_range_iff_exists_finsupp]
  let S := FiniteVectors.orbitSubrepresentation ρ w
  have hne : S ≠ ⊥ := by
    intro h
    have hmem : w ∈ S.toSubmodule := FiniteVectors.self_mem_orbitSpan ρ w
    rw [h] at hmem
    exact hw hmem
  have htop := (eq_bot_or_eq_top S).resolve_left hne
  have hv : v ∈ (⊤ : Subrepresentation ρ).toSubmodule := Submodule.mem_top
  rw [← htop] at hv
  exact hv

/-- **Intertwining by finite averaging.** -/
theorem exists_forall_conj_mem_eq_one (ρ : Representation ℂ G V) [ρ.IsIrreducible]
    {H J N : Subgroup G} {χ : G → ℂ} (hN : N.relIndex H ≠ 0)
    (hJ : ∀ g : G, (J.comap (MulAut.conj g⁻¹).toMonoidHom).relIndex H ≠ 0)
    {v w : V} (hv : v ≠ 0) (hvχ : ∀ h ∈ H, ρ h v = χ h • v)
    (hχN : ∀ h ∈ H, h ∈ N → χ h = 1) (hw : w ≠ 0) (hwJ : ∀ j ∈ J, ρ j w = w) :
    ∃ g : G, ∀ h ∈ H, g⁻¹ * h * g ∈ J → χ h = 1 := by
  classical
  by_contra hcon
  push Not at hcon
  -- `χ` is multiplicative and nonvanishing on `H`
  have hχmul : ∀ h₁ ∈ H, ∀ h₂ ∈ H, χ (h₁ * h₂) = χ h₁ * χ h₂ := by
    intro h₁ h₁H h₂ h₂H
    have e1 := hvχ _ (mul_mem h₁H h₂H)
    rw [map_mul, Module.End.mul_apply, hvχ _ h₂H, map_smul, hvχ _ h₁H, smul_smul] at e1
    exact smul_left_injective ℂ hv (e1.symm.trans (by rw [mul_comm]))
  have hχone : χ 1 = 1 := by
    have e1 := hvχ 1 (one_mem H)
    rw [map_one, Module.End.one_apply] at e1
    exact smul_left_injective ℂ hv (by simpa using e1.symm)
  have hχne : ∀ h ∈ H, χ h ≠ 0 := by
    intro h hH h0
    have := hχmul h hH h⁻¹ (inv_mem hH)
    rw [mul_inv_cancel, hχone, h0, zero_mul] at this
    exact one_ne_zero this
  -- write `v` in terms of translates of `w`
  obtain ⟨c, hc⟩ := exists_finsupp_sum_eq ρ hw v
  -- the subgroup `S`
  let T : Subgroup G := N ⊓ ⨅ g : c.support, J.comap (MulAut.conj (g : G)⁻¹).toMonoidHom
  have hT : T.relIndex H ≠ 0 :=
    Subgroup.relIndex_inf_ne_zero hN (Subgroup.relIndex_iInf_ne_zero fun g => hJ g)
  have : (T.subgroupOf H).FiniteIndex := ⟨hT⟩
  let S : Subgroup H := (T.subgroupOf H).normalCore
  have hSN : ∀ s : H, s ∈ S → (s : G) ∈ N := fun s hs =>
    (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 (Subgroup.normalCore_le (T.subgroupOf H) hs))).1
  have hSJ : ∀ s : H, s ∈ S → ∀ g ∈ c.support, g⁻¹ * (s : G) * g ∈ J := by
    intro s hs g hg
    have h1 := (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1
      (Subgroup.normalCore_le (T.subgroupOf H) hs))).2
    have h2 := (Subgroup.mem_iInf.1 h1) ⟨g, hg⟩
    simpa [MulAut.conj_apply] using h2
  let Q := H ⧸ S
  have : Finite Q := Subgroup.finite_quotient_of_finiteIndex
  let : Fintype Q := Fintype.ofFinite Q
  -- the averaging operator
  let E : Module.End ℂ V := ∑ q : Q, (χ ((Quotient.out q : H) : G))⁻¹ • ρ ((Quotient.out q : H) : G)
  have hE : ∀ x, E x = ∑ q : Q, (χ ((Quotient.out q : H) : G))⁻¹ • ρ ((Quotient.out q : H) : G) x := by
    intro x
    simp [E, LinearMap.sum_apply]
  -- the summand depends only on the coset, for `S`-fixed vectors
  have hcoset : ∀ x : V, (∀ s : H, s ∈ S → ρ s x = x) → ∀ h₁ h₂ : H,
      (QuotientGroup.mk h₁ : Q) = QuotientGroup.mk h₂ →
      (χ (h₁ : G))⁻¹ • ρ (h₁ : G) x = (χ (h₂ : G))⁻¹ • ρ (h₂ : G) x := by
    intro x hx h₁ h₂ hq
    rw [QuotientGroup.eq] at hq
    have hh₂ : h₂ = h₁ * (h₁⁻¹ * h₂) := by group
    rw [hh₂, Subgroup.coe_mul, hχmul _ h₁.2 _ (h₁⁻¹ * h₂).2, map_mul, Module.End.mul_apply,
      hx _ hq, hχN _ (h₁⁻¹ * h₂).2 (hSN _ hq), mul_one]
  -- `E v = [H : S] v`
  have hEv : E v = (Fintype.card Q : ℂ) • v := by
    rw [hE]
    have : ∀ q : Q, (χ ((Quotient.out q : H) : G))⁻¹ • ρ ((Quotient.out q : H) : G) v = v := by
      intro q
      rw [hvχ _ (Quotient.out q).2, smul_smul, inv_mul_cancel₀ (hχne _ (Quotient.out q).2),
        one_smul]
    simp only [this, Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
  -- `E (ρ g w) = 0`
  have hEw : ∀ g ∈ c.support, E (ρ g w) = 0 := by
    intro g hg
    obtain ⟨h₀, h₀H, h₀J, h₀χ⟩ := hcon g
    set x := ρ g w with hx
    have hfix : ∀ k : G, g⁻¹ * k * g ∈ J → ρ k x = x := by
      intro k hk
      calc ρ k x = ρ (k * g) w := by rw [hx, map_mul, Module.End.mul_apply]
        _ = ρ (g * (g⁻¹ * k * g)) w := by congr 2; group
        _ = ρ g (ρ (g⁻¹ * k * g) w) := by rw [map_mul, Module.End.mul_apply]
        _ = x := by rw [hwJ _ hk]
    have hxS : ∀ s : H, s ∈ S → ρ s x = x := fun s hs => hfix _ (hSJ s hs g hg)
    have hshift : E x = (χ h₀)⁻¹ • E x := by
      rw [hE, Finset.smul_sum]
      rw [← Equiv.sum_comp (Equiv.mulRight (QuotientGroup.mk ⟨h₀, h₀H⟩ : Q))]
      refine Finset.sum_congr rfl fun q _ => ?_
      simp only [Equiv.coe_mulRight]
      have hq : (QuotientGroup.mk (Quotient.out (q * QuotientGroup.mk ⟨h₀, h₀H⟩) : H) : Q) =
          QuotientGroup.mk (Quotient.out q * ⟨h₀, h₀H⟩) := by
        rw [QuotientGroup.out_eq', QuotientGroup.mk_mul, QuotientGroup.out_eq']
      rw [hcoset x hxS _ _ hq, Subgroup.coe_mul, hχmul _ (Quotient.out q).2 _ h₀H, map_mul,
        Module.End.mul_apply]
      rw [hfix h₀ h₀J, mul_inv, mul_comm, smul_smul]
    have h1 : (1 - (χ h₀)⁻¹) • E x = 0 := by
      rw [sub_smul, one_smul, ← hshift, sub_self]
    have h2 : (1 - (χ h₀)⁻¹) ≠ 0 := by
      intro h
      apply h₀χ
      have h' : (χ h₀)⁻¹ = 1 := (sub_eq_zero.1 h).symm
      simpa using congrArg (·⁻¹) h'
    exact (smul_eq_zero.1 h1).resolve_left h2
  have hE0 : E v = 0 := by
    rw [← hc, map_finsuppSum]
    refine Finset.sum_eq_zero fun g hg => ?_
    simp only [map_smul, hEw g hg, smul_zero]
  rw [hEv] at hE0
  have hcard : (Fintype.card Q : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  exact hv ((smul_eq_zero.1 hE0).resolve_left hcard)

end Averaging

section Topology

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- An open subgroup has finite index in a compact subgroup. -/
theorem relIndex_ne_zero_of_isCompact {C O : Subgroup G} (hC : IsCompact (C : Set G))
    (hO : IsOpen (O : Set G)) : O.relIndex C ≠ 0 := by
  have : CompactSpace C := isCompact_iff_compactSpace.mp hC
  have := Subgroup.quotient_finite_of_isOpen (O.subgroupOf C) (Subgroup.subgroupOf_isOpen C O hO)
  exact Subgroup.index_ne_zero_of_finite

end Topology

end Langlands.BushnellKutzko
