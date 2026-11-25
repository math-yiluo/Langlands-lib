/-
Copyright 2026 Anthropic, PBC. Licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Adapted from the Anthropic Lean formalization of Fermat's Last Theorem, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, files
`Theorems/Thm_BrauerInduction_exists_trace_eq_sum_zsmul_induced_linearCharacter.lean` and
`P2M/Sol/S_BrauerInduction_exists_trace_eq_sum_zsmul_induced_linearCharacter.lean` (without
`BrauerProof.solomon_complex`, which is in `SolomonInduction`).
Changes: statement and proof in one file; declarations renamed into
`Langlands.FiniteRep.BrauerTrace`; the group may lie in any universe; Mathlib is imported through
the port's modules and no option is set; linter clean-ups. The paired Markdown file lists the
changes.
-/
import Langlands.Representation.Finite.SolomonInduction
import Langlands.Representation.Finite.MonomialTrace

/-!
# Brauer's induction theorem, trace form

`exists_trace_eq_sum_zsmul_induced_linearCharacter`: the trace of a complex matrix representation
`ρ : G →* GL (Fin n) ℂ` of a finite group is an integral combination of class functions induced from
linear characters of subgroups:
`trace (ρ g) = ∑ i, a i * (|H i|⁻¹ * ∑ x : G, [x⁻¹ g x ∈ H i] ψ i (x⁻¹ g x))`, with `a i ∈ ℤ`.

Proof: multiply Solomon's identity `1 = ∑ a i · Ind_{H i}^G 1` (`SolomonInduction`, `H i`
hyperelementary) by the trace character, which is a class function, to get
`trace ρ = ∑ a i · Ind_{H i}^G (Res trace ρ)`; on each hyperelementary `H i` the restricted trace is
an unsigned sum of inductions of linear characters (`MonomialTrace`, with the cyclic normal
subgroup of `H i` as the normal commutative subgroup); induction in stages and a renumbering of the
double sum finish.

The Library's form of the theorem for its representation classes is
`Langlands.FiniteRep.BrauerLattice.characterLattice` (`BrauerLatticeProof`).
-/

noncomputable section

open scoped Classical
open scoped MatrixGroups

namespace Langlands.FiniteRep.BrauerTrace

universe u

section Proof

variable {G : Type u} [Group G] [Fintype G] {n : ℕ} (ρ : G →* GL (Fin n) ℂ)

/-- The trace character of a matrix representation. -/
def matrixCharacter : G → ℂ := fun g => ((ρ g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).trace

omit [Fintype G] in
theorem matrixCharacter_conj (x g : G) :
    matrixCharacter ρ (x⁻¹ * g * x) = matrixCharacter ρ g := by
  simp only [matrixCharacter, map_mul, Units.val_mul]
  rw [Matrix.trace_mul_cycle, ← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul,
    mul_inv_cancel, one_mul]

private def ext (L : Subgroup G) (ψ : L →* ℂˣ) : G → ℂ :=
  fun x => if hx : x ∈ L then ((ψ ⟨x, hx⟩ : ℂˣ) : ℂ) else 0

theorem inducedClassFunction_ext_apply (L : Subgroup G) (ψ : L →* ℂˣ) (g : G) :
    inducedClassFunction L (ext L ψ) g =
      (Nat.card L : ℂ)⁻¹ *
        ∑ x : G, if hx : x⁻¹ * g * x ∈ L then (((ψ ⟨x⁻¹ * g * x, hx⟩ : ℂˣ) : ℂ)) else 0 := by
  rw [inducedClassFunction_apply]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : x⁻¹ * g * x ∈ L
  · rw [ite_eq_left hx, dite_eq_left hx, ext]
    rw [dite_eq_left hx]
  · rw [ite_eq_right hx, dite_eq_right hx]

/-- On a hyperelementary subgroup `H`, the induced trace character is a sum of class functions
induced from linear characters of subgroups of `G` contained in `H`. -/
theorem exists_inducedClassFunction_matrixCharacter_eq_sum (H : Subgroup G)
    (hH : ∃ q : ℕ, q.Prime ∧ ∃ C : Subgroup G, C ≤ H ∧ IsCyclic C ∧ (Nat.card C).Coprime q ∧
      (∀ h ∈ H, ∀ c ∈ C, h * c * h⁻¹ ∈ C) ∧ (∀ h ∈ H, ∃ m : ℕ, h ^ q ^ m ∈ C)) :
    ∃ (k : ℕ) (L : Fin k → Subgroup G) (ψ : (j : Fin k) → (L j →* ℂˣ)),
      ∀ g : G, inducedClassFunction H (matrixCharacter ρ) g =
        ∑ j, inducedClassFunction (L j) (ext (L j) (ψ j)) g := by
  obtain ⟨q, hq, C, hCH, hCcyc, -, hCnorm, hCpow⟩ := hH

  let A : Subgroup H := C.subgroupOf H
  have hAn : A.Normal := by
    refine ⟨fun a ha h => ?_⟩
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    simpa using hCnorm h h.2 a ha
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    intro a ha b hb
    rw [Subgroup.mem_subgroupOf] at ha hb
    have := hCcyc
    obtain ⟨g₀, hg₀⟩ := IsCyclic.exists_generator (α := C)
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 (hg₀ ⟨a, ha⟩)
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (hg₀ ⟨b, hb⟩)
    have hc : (⟨a, ha⟩ : C) * ⟨b, hb⟩ = ⟨b, hb⟩ * ⟨a, ha⟩ := by
      rw [← hi, ← hj]; exact zpow_mul_comm g₀ i j
    have hc' := congrArg Subtype.val hc
    simp only [Subgroup.coe_mul] at hc'
    exact Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul]; exact hc')
  have hApow : ∀ h : H, ∃ m : ℕ, h ^ q ^ m ∈ A := by
    intro h
    obtain ⟨m, hm⟩ := hCpow h h.2
    exact ⟨m, by rw [Subgroup.mem_subgroupOf, Subgroup.coe_pow]; exact hm⟩
  obtain ⟨k, L, ψ, hL⟩ :=
    MonomialTrace.exists_trace_eq_sum_inducedClassFunction_linearCharacter
      hq A hAn hAcomm hApow (ρ.comp H.subtype)

  set extH : (j : Fin k) → (H → ℂ) := fun j x =>
    if hx : x ∈ L j then (((ψ j) ⟨x, hx⟩ : ℂˣ) : ℂ) else 0 with hextH

  let L' : Fin k → Subgroup G := fun j => (L j).map H.subtype
  let ψ' : (j : Fin k) → (L' j →* ℂˣ) := fun j =>
    (ψ j).comp ((L j).equivMapOfInjective H.subtype H.subtype_injective).symm.toMonoidHom
  refine ⟨k, L', ψ', fun g => ?_⟩

  have step1 : inducedClassFunction H (matrixCharacter ρ) =
      inducedClassFunction H (fun x => ∑ j, (fun y : G =>
        if hy : y ∈ H then inducedClassFunction (L j) (extH j) ⟨y, hy⟩ else 0) x) := by
    apply inducedClassFunction_congr
    intro y hy
    have := hL ⟨y, hy⟩
    simp only [MonoidHom.coe_comp, Subgroup.coe_subtype, Function.comp_apply] at this
    rw [matrixCharacter]
    beta_reduce
    rw [this]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [dite_eq_left hy]
  rw [step1, inducedClassFunction_sum]
  refine Finset.sum_congr rfl fun j _ => ?_

  rw [inducedClassFunction_inducedClassFunction H (L j) (extH j)]
  apply congrFun (inducedClassFunction_congr _ ?_) g
  intro y hy
  obtain ⟨z, hz, rfl⟩ := hy
  change (if hg : (z : G) ∈ H then extH j ⟨(z : G), hg⟩ else 0) =
    ext (L' j) (ψ' j) (z : G)
  rw [dite_eq_left z.2]
  have hz' : (⟨(z : G), z.2⟩ : H) ∈ L j := by simpa using hz
  have hmem : (z : G) ∈ L' j := ⟨z, hz, rfl⟩
  simp only [hextH, ext, dite_eq_left hz', dite_eq_left hmem]
  change _ = (((ψ j) (((L j).equivMapOfInjective H.subtype H.subtype_injective).symm
    ⟨(z : G), hmem⟩) : ℂˣ) : ℂ)
  congr 2
  apply ((L j).equivMapOfInjective H.subtype H.subtype_injective).injective
  rw [MulEquiv.apply_symm_apply]
  apply Subtype.ext
  rfl

theorem exists_matrixCharacter_eq_sum_zsmul :
    ∃ (k : ℕ) (H : Fin k → Subgroup G) (ψ : (i : Fin k) → (H i →* ℂˣ)) (a : Fin k → ℤ),
      ∀ g : G, matrixCharacter ρ g =
        ∑ i, (a i : ℂ) * inducedClassFunction (H i) (ext (H i) (ψ i)) g := by
  obtain ⟨k, H, a, hH, h1⟩ :=
    Solomon.exists_one_eq_sum_zsmul_inducedClassFunction_one_complex (G := G)
  have h2 : ∀ g : G, matrixCharacter ρ g =
      ∑ i, (a i : ℂ) * inducedClassFunction (H i) (matrixCharacter ρ) g := by
    intro g
    have := congrArg (fun t => t * matrixCharacter ρ g) (h1 g)
    simp only [one_mul, Finset.sum_mul, mul_assoc] at this
    rw [this]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inducedClassFunction_mul_of_conj_invariant (H i) _ _ (matrixCharacter_conj ρ) g]
    simp only [one_mul]

  have h3 := fun i => exists_inducedClassFunction_matrixCharacter_eq_sum ρ (H i) (hH i)
  choose kf Lf ψf hf using h3

  let ι := Σ i : Fin k, Fin (kf i)
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  refine ⟨Fintype.card ι, fun m => Lf (e.symm m).1 (e.symm m).2,
    fun m => ψf (e.symm m).1 (e.symm m).2, fun m => a (e.symm m).1, fun g => ?_⟩
  rw [h2 g]
  simp_rw [hf]
  rw [← Fintype.sum_equiv e (fun s : ι => (a s.1 : ℂ) *
      inducedClassFunction (Lf s.1 s.2) (ext (Lf s.1 s.2) (ψf s.1 s.2)) g) _
      (fun s => by rw [Equiv.symm_apply_apply])]
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]

end Proof

/-- **Brauer's induction theorem, trace form.** The trace of a complex matrix representation of a
finite group is an integral combination of class functions induced from linear characters of
subgroups. -/
theorem exists_trace_eq_sum_zsmul_induced_linearCharacter
    {G : Type u} [Group G] [Fintype G] {n : ℕ} (ρ : G →* GL (Fin n) ℂ) :
    ∃ (k : ℕ) (H : Fin k → Subgroup G) (ψ : (i : Fin k) → (H i →* ℂˣ)) (a : Fin k → ℤ),
      ∀ g : G, ((ρ g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).trace =
        ∑ i : Fin k, (a i : ℂ) * ((Nat.card (H i) : ℂ)⁻¹ *
          ∑ x : G, if hx : x⁻¹ * g * x ∈ H i then (((ψ i) ⟨x⁻¹ * g * x, hx⟩ : ℂˣ) : ℂ) else 0) := by
  obtain ⟨k, H, ψ, a, h⟩ := exists_matrixCharacter_eq_sum_zsmul ρ
  refine ⟨k, H, ψ, a, fun g => ?_⟩
  have := h g
  rw [matrixCharacter] at this
  rw [this]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inducedClassFunction_ext_apply]

end Langlands.FiniteRep.BrauerTrace

end
