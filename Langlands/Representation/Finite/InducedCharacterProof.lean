import Langlands.Representation.Finite.BrauerStatement

/-!
# Degree and character of actual finite-index induction

Proofs of `Langlands.FiniteRep.FiniteRankOneOrderStatement`,
`Langlands.FiniteRep.FiniteInducedDegreeStatement` and
`Langlands.FiniteRep.FiniteInducedCharacterFormulaStatement`.
-/

noncomputable section

namespace Langlands.FiniteRep.InducedCharacter

open Module

universe u v uG

section RankOne

theorem rankOneOrder (G : Type uG) [Group G] [Fintype G] : FiniteRankOneOrderStatement G := by
  intro S χ s
  rw [← map_pow, pow_card_eq_one', map_one]

end RankOne

section Coordinates

variable {k : Type u} [Field k] {G : Type v} [Group G] (S : Subgroup G)

/-- Right cosets `S g` of `S`. -/
abbrev RightCoset := Quotient (QuotientGroup.rightRel S)

/-- The class of `g` in the right cosets. -/
abbrev rightCoset (g : G) : RightCoset S := Quotient.mk _ g

theorem mul_out_inv_mem (g : G) {q : RightCoset S} (hq : rightCoset S g = q) :
    g * q.out⁻¹ ∈ S := by
  subst hq
  exact QuotientGroup.rightRel_apply.mp (Quotient.exact (Quotient.out_eq (rightCoset S g)))

theorem rightCoset_eq_iff (a b : G) : rightCoset S a = rightCoset S b ↔ b * a⁻¹ ∈ S :=
  Quotient.eq.trans QuotientGroup.rightRel_apply

theorem rightCoset_mul (s : S) (g : G) : rightCoset S ((s : G) * g) = rightCoset S g := by
  rw [rightCoset_eq_iff]
  simp

/-- The element `g * q.out⁻¹` of `S`, when `g` lies in the coset `q`. -/
def factor (g : G) (q : RightCoset S) (hq : rightCoset S g = q) : S :=
  ⟨g * q.out⁻¹, mul_out_inv_mem S g hq⟩

theorem factor_mul_out (g : G) (q : RightCoset S) (hq : rightCoset S g = q) :
    (factor S g q hq : G) * q.out = g := by
  simp [factor]

variable (V : FDRep k S)

/-- Extension of a function on right cosets to an equivariant function on `G`. -/
def extend (F : RightCoset S → V) : Representation.coindV S.subtype V.ρ :=
  ⟨fun g => V.ρ (factor S g _ rfl) (F (rightCoset S g)), by
    intro s g
    change V.ρ (factor S (s * g) _ rfl) (F (rightCoset S (s * g))) =
      V.ρ s (V.ρ (factor S g _ rfl) (F (rightCoset S g)))
    have h := rightCoset_mul S s g
    have hf : factor S ((s : G) * g) _ rfl = s * factor S g _ rfl := Subtype.ext (by
      change (s : G) * g * (rightCoset S ((s : G) * g)).out⁻¹ =
        (s : G) * (g * (rightCoset S g).out⁻¹)
      rw [h, mul_assoc])
    rw [hf, map_mul, Module.End.mul_apply, h]⟩

theorem extend_apply (F : RightCoset S → V) (g : G) (q : RightCoset S)
    (hq : rightCoset S g = q) :
    (extend S V F).1 g = V.ρ (factor S g q hq) (F q) := by
  subst hq
  rfl

/-- Coinduced vectors are determined by their values on right-coset representatives. -/
def coordEquiv : Representation.coindV S.subtype V.ρ ≃ₗ[k] (RightCoset S → V) where
  toLinearMap := coindEvaluation S V
  invFun := extend S V
  left_inv f := by
    apply Subtype.ext
    funext g
    change (extend S V (fun q => f.1 q.out)).1 g = f.1 g
    rw [extend_apply S V _ g _ rfl]
    conv_rhs => rw [← factor_mul_out S g _ rfl]
    exact (f.2 _ _).symm
  right_inv F := by
    funext q
    change (extend S V F).1 q.out = F q
    rw [extend_apply S V F q.out q (Quotient.out_eq q)]
    have h1 : factor S q.out q (Quotient.out_eq q) = 1 := Subtype.ext (by simp [factor])
    rw [h1, map_one, Module.End.one_apply]

@[simp]
theorem coordEquiv_apply (f : Representation.coindV S.subtype V.ρ) (q : RightCoset S) :
    coordEquiv S V f q = f.1 q.out := rfl

@[simp]
theorem coordEquiv_symm_apply (F : RightCoset S → V) (g : G) :
    ((coordEquiv S V).symm F).1 g = V.ρ (factor S g _ rfl) (F (rightCoset S g)) := rfl

theorem natCard_rightCoset : Nat.card (RightCoset S) = S.index := by
  rw [Subgroup.index_eq_card]
  exact Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel S)

end Coordinates

section Degree

variable (G : Type uG) [Group G] [Fintype G]

theorem inducedDegree : FiniteInducedDegreeStatement G := by
  intro S V
  have : Finite (RightCoset S) := Quotient.finite _
  let : Fintype (RightCoset S) := Fintype.ofFinite _
  rw [← (induceRepEquiv S V).toLinearEquiv.finrank_eq,
    (indCoindEquiv S V).toLinearEquiv.finrank_eq, (coordEquiv S V).finrank_eq,
    Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    ← Nat.card_eq_fintype_card, natCard_rightCoset]

end Degree

section Trace

variable {k : Type u} [Field k] {ι : Type v} [Fintype ι] [DecidableEq ι]
variable {M : Type*} [AddCommGroup M] [Module k M] [Module.Finite k M]

/-- The trace of a block-monomial endomorphism of `ι → M`: only the blocks fixed by the
index map contribute. -/
theorem trace_pi_monomial (π : ι → ι) (A : ι → M →ₗ[k] M) :
    LinearMap.trace k (ι → M)
        (∑ i, LinearMap.single k (fun _ => M) i ∘ₗ A i ∘ₗ LinearMap.proj (π i)) =
      ∑ i, if π i = i then LinearMap.trace k M (A i) else 0 := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.trace_comp_comm', LinearMap.comp_assoc]
  split_ifs with h
  · rw [h, LinearMap.proj_comp_single_same (R := k) (φ := fun _ : ι => M) i,
      LinearMap.comp_id]
  · rw [LinearMap.proj_comp_single_ne (R := k) (φ := fun _ : ι => M) (π i) i h,
      LinearMap.comp_zero, map_zero]

end Trace

section CharacterFormula

variable {G : Type uG} [Group G] [Fintype G]

open Classical in
/-- The trace of the coinduced action, computed on right-coset coordinates. -/
theorem coind_character (S : Subgroup G) (V : FDRep ℂ S) (g : G) :
    (Representation.coind S.subtype V.ρ).character g =
      ∑ q : RightCoset S,
        if h : q.out * g * q.out⁻¹ ∈ S then V.character ⟨q.out * g * q.out⁻¹, h⟩ else 0 := by
  let e := coordEquiv S V
  let π : RightCoset S → RightCoset S := fun q => rightCoset S (q.out * g)
  let A : RightCoset S → V →ₗ[ℂ] V := fun q => V.ρ (factor S (q.out * g) (π q) rfl)
  have hT : e.conj (Representation.coind S.subtype V.ρ g) =
      ∑ q, LinearMap.single ℂ (fun _ => V) q ∘ₗ A q ∘ₗ LinearMap.proj (π q) := by
    refine LinearMap.ext fun F => funext fun q => ?_
    rw [LinearEquiv.conj_apply_apply, LinearMap.sum_apply, Finset.sum_apply,
      Finset.sum_eq_single q]
    · change ((coordEquiv S V).symm F).1 (q.out * g) =
        (LinearMap.single ℂ (fun _ => V) q (A q (F (π q)))) q
      rw [LinearMap.single_apply, Pi.single_eq_same]
      rfl
    · intro b _ hb
      rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.single_apply,
        Pi.single_eq_of_ne (Ne.symm hb)]
    · intro h
      exact absurd (Finset.mem_univ q) h
  rw [Representation.character, ← LinearMap.trace_conj' _ e, hT, trace_pi_monomial]
  refine Finset.sum_congr rfl fun q _ => ?_
  have hiff : π q = q ↔ q.out * g * q.out⁻¹ ∈ S := by
    change rightCoset S (q.out * g) = q ↔ _
    conv_lhs => rw [← Quotient.out_eq q]
    rw [rightCoset_eq_iff]
    constructor
    · intro h
      simpa [mul_assoc] using S.inv_mem h
    · intro h
      simpa [mul_assoc] using S.inv_mem h
  by_cases h : q.out * g * q.out⁻¹ ∈ S
  · rw [ite_eq_left (hiff.mpr h), dite_eq_left h]
    have hf : factor S (q.out * g) (π q) rfl = ⟨q.out * g * q.out⁻¹, h⟩ := Subtype.ext (by
      change q.out * g * (π q).out⁻¹ = q.out * g * q.out⁻¹
      rw [hiff.mpr h])
    change LinearMap.trace ℂ V (V.ρ (factor S (q.out * g) (π q) rfl)) = _
    rw [hf]
    rfl
  · rw [ite_eq_right (mt hiff.mp h), dite_eq_right h]

open Classical in
theorem inducedCharacterFormula : FiniteInducedCharacterFormulaStatement G := by
  intro S V g
  let φ : G → ℂ := fun y =>
    if h : y * g * y⁻¹ ∈ S then V.character ⟨y * g * y⁻¹, h⟩ else 0
  have hφ (s : S) (y : G) : φ ((s : G) * y) = φ y := by
    have hmem : (s : G) * y * g * ((s : G) * y)⁻¹ ∈ S ↔ y * g * y⁻¹ ∈ S := by
      constructor
      · intro h
        have := S.mul_mem (S.mul_mem (S.inv_mem s.2) h) s.2
        simpa [mul_assoc] using this
      · intro h
        have := S.mul_mem (S.mul_mem s.2 h) (S.inv_mem s.2)
        simpa [mul_assoc] using this
    by_cases h : y * g * y⁻¹ ∈ S
    · simp only [φ, dite_eq_left h, dite_eq_left (hmem.mpr h)]
      have := FDRep.char_conj V ⟨y * g * y⁻¹, h⟩ s
      rw [← this]
      congr 1
      exact Subtype.ext (by simp [mul_assoc])
    · simp only [φ, dite_eq_right h, dite_eq_right (mt hmem.mp h)]
  -- `G` is in bijection with `S × (right cosets)`.
  let E : S × RightCoset S ≃ G :=
    { toFun := fun p => (p.1 : G) * p.2.out
      invFun := fun y => (factor S y _ rfl, rightCoset S y)
      left_inv := by
        rintro ⟨s, q⟩
        have hq : rightCoset S ((s : G) * q.out) = q := by
          rw [rightCoset_mul]
          exact Quotient.out_eq q
        ext
        · change (s : G) * q.out * (rightCoset S ((s : G) * q.out)).out⁻¹ = s
          rw [hq, mul_inv_cancel_right]
        · exact hq
      right_inv := fun y => factor_mul_out S y _ rfl }
  have hsum : ∑ y : G, φ y = (Nat.card S : ℂ) * ∑ q : RightCoset S, φ q.out := by
    rw [← E.sum_comp, Fintype.sum_prod_type]
    simp only [E, Equiv.coe_fn_mk, hφ, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [Nat.card_eq_fintype_card]
  have hinv : ∑ x : G, (if h : x⁻¹ * g * x ∈ S then V.character ⟨x⁻¹ * g * x, h⟩ else 0) =
      ∑ y : G, φ y := by
    refine Fintype.sum_equiv (Equiv.inv G) _ _ fun x => ?_
    simp [φ]
  have hS : (Nat.card S : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  rw [hinv, hsum, ← mul_assoc, inv_mul_cancel₀ hS, one_mul]
  change LinearMap.trace ℂ _ ((induceRep S V).ρ g) = _
  rw [← Representation.character, ← Representation.char_iso (induceRepEquiv S V),
    Representation.char_iso (indCoindEquiv S V), coind_character]

end CharacterFormula

/-- The rank-one, degree and character-formula conjuncts of Henniart's finite Brauer input. -/
theorem inducedConjuncts (G : Type uG) [Group G] [Fintype G] :
    FiniteRankOneOrderStatement G ∧ FiniteInducedCharacterFormulaStatement G ∧
      FiniteInducedDegreeStatement G :=
  ⟨rankOneOrder G, inducedCharacterFormula, inducedDegree G⟩

end Langlands.FiniteRep.InducedCharacter
