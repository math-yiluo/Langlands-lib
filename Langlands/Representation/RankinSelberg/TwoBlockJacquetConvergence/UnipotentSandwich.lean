import Langlands.Group.GL.PrincipalLevelDominance

/-!
# Dominant torus sandwiches with a unipotent left factor

For a positive principal level `P = K(a)` of `GL_(n+1)`, antitone exponents `lam₁, lam₂` and
`g ∈ P`, one has `ϖ^lam₁ g ϖ^lam₂ = x (ϖ^lam₁ ϖ^lam₂) y` with `x ∈ P` upper unipotent and
`y ∈ P`. This refines `Langlands.GeneralLinear.exists_dominant_sandwich`, whose proof is
followed: the left factor there is `x d` with `d` diagonal in `P`, and `d` is moved to the
right since it commutes with diagonal matrices.
-/

noncomputable section

namespace Langlands.RankinSelberg.TwoBlockConvergence

open Matrix Langlands.Conductor Langlands.GeneralLinear

universe u

section Sandwich

variable {k : Type u} [Field k] [ValuativeRel k]

omit [ValuativeRel k] in
/-- Conjugating an upper unipotent matrix by a diagonal matrix keeps it upper unipotent. -/
theorem diagonalUnits_conj_mem_upperUnipotent {n : ℕ} (d : Fin n → kˣ)
    {x : GeneralLinear n k} (hx : x ∈ upperUnipotent n k) :
    Iwasawa.diagonalUnits d * x * (Iwasawa.diagonalUnits d)⁻¹ ∈ upperUnipotent n k := by
  have hinv : (Iwasawa.diagonalUnits d)⁻¹ = Iwasawa.diagonalUnits (fun i => (d i)⁻¹) := by
    rw [← map_inv]
    rfl
  rw [hinv]
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · change (Iwasawa.diagonalUnits d * x * Iwasawa.diagonalUnits (fun i => (d i)⁻¹)) i j = 0
    rw [Iwasawa.diagonalUnits_mul_mul_apply, hx.1 hij, mul_zero, zero_mul]
  · rw [Iwasawa.diagonalUnits_mul_mul_apply, hx.2 i, mul_one, Units.mul_inv]

/-- **Unipotent dominant sandwich.** For a positive principal level `P` and antitone
exponents, `ϖ^lam₁ g ϖ^lam₂ ∈ (P ∩ N) (ϖ^lam₁ ϖ^lam₂) P` for every `g ∈ P`. -/
theorem exists_unipotent_sandwich {n a : ℕ} (ha : 0 < a) {ϖ : kˣ}
    (hϖ : ValuativeRel.valuation k (ϖ : k) ≤ 1) {lam₁ lam₂ : Fin (n + 1) → ℤ}
    (h₁ : Antitone lam₁) (h₂ : Antitone lam₂) {g : GeneralLinear (n + 1) k}
    (hg : g ∈ principalLevelSubgroup k n a) :
    ∃ x ∈ principalLevelSubgroup k n a, x ∈ upperUnipotent (n + 1) k ∧
      ∃ y ∈ principalLevelSubgroup k n a,
        Iwasawa.torus ϖ lam₁ * g * Iwasawa.torus ϖ lam₂ =
          x * (Iwasawa.torus ϖ lam₁ * Iwasawa.torus ϖ lam₂) * y := by
  set S := BlockShape.singletons (n + 1)
  set P := principalLevelSubgroup k n a
  obtain ⟨⟨l, d, u⟩, hldu⟩ :=
    BlockShape.principalLevelSubgroup_iwahoriProduct_surjective k n S a ha ⟨g⁻¹, inv_mem hg⟩
  have hval := congrArg Subtype.val hldu
  rw [BlockShape.iwahoriProduct_val] at hval
  have hgeq : g = u.val⁻¹ * d.val⁻¹ * l.val⁻¹ := by
    rw [← _root_.mul_inv_rev, ← _root_.mul_inv_rev, ← mul_assoc, hval, inv_inv]
  obtain ⟨hlP, hlS⟩ := Subgroup.mem_inf.mp l.property
  obtain ⟨hdP, hdS⟩ := Subgroup.mem_inf.mp d.property
  obtain ⟨huP, huS⟩ := Subgroup.mem_inf.mp u.property
  have hδ₁ := torus_eq_blockScalar ϖ lam₁
  have hδ₂ := torus_eq_blockScalar ϖ lam₂
  set δ₁ := S.blockScalar k (fun i => ϖ ^ lam₁ i)
  set δ₂ := S.blockScalar k (fun i => ϖ ^ lam₂ i)
  -- the Levi factor commutes with the block scalar `δ₂`
  have hcomm : δ₂ * d.val⁻¹ = d.val⁻¹ * δ₂ := by
    obtain ⟨m₀, hm₀⟩ := (S.leviSubgroup k).inv_mem hdS
    rw [← hm₀]
    change S.leviEmbedding k (S.blockScalarLevi k _) * _ =
      _ * S.leviEmbedding k (S.blockScalarLevi k _)
    rw [← map_mul, ← map_mul, S.blockScalarLevi_commute]
  have huN : u.val⁻¹ ∈ upperUnipotent (n + 1) k := by
    rw [← BlockShape.singletons_unipotentSubgroup]
    exact (S.unipotentSubgroup k).inv_mem huS
  refine ⟨δ₁ * u.val⁻¹ * δ₁⁻¹, ?_, ?_, d.val⁻¹ * (δ₂⁻¹ * l.val⁻¹ * δ₂), ?_, ?_⟩
  · exact principal_upper_conj S _ _ _ (ratio_mem_integer hϖ h₁)
      ((S.unipotentSubgroup k).inv_mem huS) (inv_mem huP)
  · rw [← hδ₁]
    exact diagonalUnits_conj_mem_upperUnipotent _ huN
  · refine mul_mem (inv_mem hdP) ?_
    exact principal_lower_inv_conj S _ _ _ (ratio_mem_integer hϖ h₂)
      ((S.oppositeUnipotentSubgroup k).inv_mem hlS) (inv_mem hlP)
  · rw [hδ₁, hδ₂, hgeq]
    have h' : δ₂ * d.val⁻¹ * δ₂⁻¹ = d.val⁻¹ := by
      rw [hcomm]
      group
    calc
      δ₁ * (u.val⁻¹ * d.val⁻¹ * l.val⁻¹) * δ₂ =
          δ₁ * u.val⁻¹ * (δ₂ * d.val⁻¹ * δ₂⁻¹) * l.val⁻¹ * δ₂ := by
        rw [h']
        group
      _ = _ := by group

end Sandwich

end Langlands.RankinSelberg.TwoBlockConvergence
