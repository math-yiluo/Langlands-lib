import Langlands.Representation.FiniteGeneralLinear.FiniteCharacterMultiplicity
import Mathlib.Algebra.DirectSum.LinearMap

/-! # Multiplicity-free finite representations -/

noncomputable section

open Module Representation
open scoped DirectSum

namespace Langlands.FiniteRep

open VirtualCharacter

variable {G : Type*} [Group G]

/-- Irreducible classes receiving a nonzero intertwiner from the given representation. -/
def ConstituentClass (V : FDRep ℂ G) :=
  {a : IrreducibleClass G // 0 < finrank ℂ (IntertwiningMap V.ρ (rep a).ρ)}

instance [Finite G] (V : FDRep ℂ G) : Finite (ConstituentClass V) :=
  inferInstanceAs (Finite {a : IrreducibleClass G // 0 < finrank ℂ (IntertwiningMap V.ρ (rep a).ρ)})

section CoordinateProjections

variable {ι : Type*} [DecidableEq ι] {M : ι → Type*}
  [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
  (ρ : ∀ i, Representation ℂ G (M i))

private def sumInclude (i : ι) : IntertwiningMap (ρ i) (Representation.directSum ρ) where
  toLinearMap := DirectSum.lof ℂ ι M i
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    simp [Representation.directSum_apply]

private def sumProject (i : ι) : IntertwiningMap (Representation.directSum ρ) (ρ i) where
  toLinearMap := DirectSum.component ℂ ι M i
  isIntertwining' g := by
    apply DirectSum.linearMap_ext ℂ
    intro j
    apply LinearMap.ext
    intro v
    simp only [LinearMap.comp_apply, Representation.directSum_apply, DirectSum.lmap_lof]
    by_cases h : j = i
    · subst j
      simp
    · simp [DirectSum.component.of, h]

private theorem sumProject_include_same (i : ι) (v : M i) :
    sumProject ρ i (sumInclude ρ i v) = v :=
  DirectSum.component.lof_self ℂ i v

private theorem sumProject_include_ne {i j : ι} (h : j ≠ i) (v : M j) :
    sumProject ρ i (sumInclude ρ j v) = 0 := by
  change DirectSum.component ℂ ι M i (DirectSum.lof ℂ ι M j v) = 0
  rw [DirectSum.component.of, dite_eq_right h]

private theorem no_equiv_between_summands {A : Type*} [AddCommGroup A] [Module ℂ A]
    {σ : Representation ℂ G A} (e : Representation.Equiv (Representation.directSum ρ) σ)
    (hc : ∀ S T : IntertwiningMap σ σ, S * T = T * S)
    {i j : ι} [Nontrivial (M j)] (h : i ≠ j) (f : Representation.Equiv (ρ i) (ρ j)) : False := by
  let I (l : ι) := e.toIntertwiningMap.comp (sumInclude ρ l)
  let P (l : ι) := (sumProject ρ l).comp e.symm.toIntertwiningMap
  let S := (I j).comp ((f.toIntertwiningMap).comp (P i))
  let T := (I i).comp (P i)
  obtain ⟨v, hv⟩ := exists_ne (0 : M j)
  have hcomm := DFunLike.congr_fun (hc S T) (I i (f.symm v))
  have same (l : ι) (x : M l) : P l (I l x) = x := by
    simp [P, I, sumProject_include_same]
  have off (x : M j) : P i (I j x) = 0 := by
    simp [P, I, sumProject_include_ne ρ h.symm]
  have hzero : I j v = 0 := by
    simpa only [IntertwiningMap.mul_apply, S, T, IntertwiningMap.comp_apply, same,
      Representation.Equiv.coe_toIntertwiningMap, Representation.Equiv.apply_symm_apply, off,
      map_zero] using hcomm
  apply hv
  have he := congrArg (P j) hzero
  simpa only [same, map_zero] using he

end CoordinateProjections

section FiniteGroup

variable [Fintype G]

private theorem pairing_sum_left {ι : Type*} [Fintype ι] (f : ι → G → ℂ) (h : G → ℂ) :
    pairing (∑ i, f i) h = ∑ i, pairing (f i) h := by
  change (Fintype.card G : ℂ)⁻¹ * ∑ g : G, (∑ i, f i) g⁻¹ * h g = _
  simp only [Finset.sum_apply, Finset.sum_mul, Finset.mul_sum]
  change (∑ g : G, ∑ i, (Fintype.card G : ℂ)⁻¹ * (f i g⁻¹ * h g)) =
    ∑ i, (Fintype.card G : ℂ)⁻¹ * ∑ g : G, f i g⁻¹ * h g
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

private theorem constituentClass_of_decomposition (V : FDRep ℂ G) {n : ℕ}
    (a : Fin n → IrreducibleClass G) (ha : Function.Injective a)
    (hc : V.character = ∑ i, character (a i).1) :
    (∀ b : IrreducibleClass G, finrank ℂ (IntertwiningMap V.ρ (rep b).ρ) ≤ 1) ∧
      Nat.card (ConstituentClass V) = finrank ℂ (IntertwiningMap V.ρ V.ρ) := by
  classical
  have h_one (b : IrreducibleClass G) :
      finrank ℂ (IntertwiningMap V.ρ (rep b).ρ) = ∑ i, if a i = b then 1 else 0 := by
    apply Nat.cast_injective (R := ℂ)
    rw [Nat.cast_sum, ← FiniteCharacter.card_inv_mul_sum_eq_finrank]
    change pairing V.character (rep b).character = _
    rw [hc, ← character_val, pairing_sum_left]
    simp only [pairing_irreducible, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  have h_ind (b : IrreducibleClass G) :
      finrank ℂ (IntertwiningMap V.ρ (rep b).ρ) = if b ∈ Set.range a then 1 else 0 := by
    rw [h_one]
    by_cases hb : b ∈ Set.range a
    · rw [ite_eq_left hb]
      obtain ⟨i, rfl⟩ := hb
      simp [ha.eq_iff]
    · rw [ite_eq_right hb]
      apply Finset.sum_eq_zero
      intro i _
      exact ite_eq_right (fun hi => hb ⟨i, hi⟩)
  have h_end : finrank ℂ (IntertwiningMap V.ρ V.ρ) = n := by
    apply Nat.cast_injective (R := ℂ)
    rw [← FiniteCharacter.card_inv_mul_sum_eq_finrank]
    change pairing V.character V.character = _
    nth_rewrite 2 [hc]
    rw [map_sum]
    have hone (i : Fin n) : pairing V.character (character (a i).1) = 1 := by
      rw [character_val]
      change (Fintype.card G : ℂ)⁻¹ *
        ∑ g : G, Representation.character V.ρ g⁻¹ * Representation.character (rep (a i)).ρ g = 1
      rw [FiniteCharacter.card_inv_mul_sum_eq_finrank, h_ind, ite_eq_left ⟨i, rfl⟩, Nat.cast_one]
    simp [hone]
  refine ⟨fun b => ?_, ?_⟩
  · rw [h_ind]
    split <;> omega
  · rw [h_end]
    let e : Fin n ≃ ConstituentClass V := Equiv.ofBijective
      (fun i => ⟨a i, by rw [h_ind, ite_eq_left ⟨i, rfl⟩]; decide⟩)
      ⟨fun i j h => ha (congrArg Subtype.val h), fun b => by
        have hb := b.2
        rw [h_ind] at hb
        by_cases hr : b.1 ∈ Set.range a
        · obtain ⟨i, hi⟩ := hr
          exact ⟨i, Subtype.ext hi⟩
        · simp [hr] at hb⟩
    rw [← Nat.card_congr e, Nat.card_fin]

/-- A finite complex representation with commuting endomorphisms has multiplicity at most one.
Its endomorphism dimension counts its constituent classes. -/
theorem multiplicityFree_of_commuting (V : FDRep ℂ G)
    (hc : ∀ S T : IntertwiningMap V.ρ V.ρ, S * T = T * S) :
    (∀ b : IrreducibleClass G, finrank ℂ (IntertwiningMap V.ρ (rep b).ρ) ≤ 1) ∧
      Nat.card (ConstituentClass V) = finrank ℂ (IntertwiningMap V.ρ V.ρ) := by
  classical
  obtain ⟨n, S, ha, hi, htop⟩ := FiniteCharacter.exists_decomposition V.ρ
  let ρ (i : Fin n) := (S i).toRepresentation
  have hir (i : Fin n) : (ρ i).IsIrreducible :=
    FiniteIndexRestriction.isIrreducible_toRepresentation_of_isAtom _ (ha i)
  have hi' : DirectSum.IsInternal fun i => (S i).toSubmodule :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top (FiniteCharacter.iSupIndep_toSubmodule hi) (by
      rw [← Langlands.Subrepresentation.toSubmodule_iSup, htop]
      rfl)
  let e : Representation.Equiv (Representation.directSum ρ) V.ρ :=
    Representation.Equiv.mk (LinearEquiv.ofBijective (DirectSum.coeLinearMap _) hi') fun g => by
      refine DirectSum.linearMap_ext ℂ fun i => LinearMap.ext fun x => ?_
      change DirectSum.coeLinearMap (fun j => (S j).toSubmodule)
          (Representation.directSum ρ g (DirectSum.lof ℂ (Fin n) _ i x)) =
        V.ρ g (DirectSum.coeLinearMap (fun j => (S j).toSubmodule) (DirectSum.lof ℂ (Fin n) _ i x))
      rw [Representation.directSum_apply, DirectSum.lmap_lof, DirectSum.coeLinearMap_lof,
        DirectSum.coeLinearMap_lof]
      rfl
  let a : Fin n → IrreducibleClass G := fun i =>
    ⟨classOfRepresentation (ρ i), ofRepresentation (ρ i), rfl,
      VirtualCharacter.isIrreducible_of_equiv (modelEquiv (ρ i)) (hir i)⟩
  have hag : Function.Injective a := by
    intro i j hij
    by_contra hne
    have hcl := congrArg Subtype.val hij
    change classOfRepresentation (ρ i) = classOfRepresentation (ρ j) at hcl
    obtain ⟨f⟩ := (classOfRepresentation_eq_iff _ _).mp hcl
    let : Nontrivial ((S j).toSubmodule) :=
      Submodule.nontrivial_iff_ne_bot.mpr (FiniteCharacter.toSubmodule_ne_bot (ha j).ne_bot)
    exact no_equiv_between_summands ρ e hc hne f
  apply constituentClass_of_decomposition V a hag
  funext g
  rw [Finset.sum_apply]
  have ht := LinearMap.trace_eq_sum_trace_restrict hi' (f := V.ρ g)
    (fun i _ hx => (S i).apply_mem_toSubmodule g hx)
  change V.character g = ∑ i, Representation.character (ρ i) g at ht
  rw [ht]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact (congrFun (character_classOfRepresentation (ρ i)) g).symm

end FiniteGroup

end Langlands.FiniteRep
