import Langlands.Global.Arithmetic.HarrisProposition48MackeyTransportStatement

/-!
# The fibres of the prime-orbit Mackey index in Harris's Proposition 4.8

Proof of `Proposition48MackeyFibreStatement`: in a prime cyclic step `D` with
`[D : E]` double cosets `Gal(L/D) \ Gal(L/E) / Gal(L/E')`, the field `D` lies in
`E'` and the double cosets are the fibres of restriction to `D`.
-/

noncomputable section

universe uF

set_option autoImplicit false

namespace Langlands.Global.Harris

/-- Harris (1998), proof of Proposition 4.8 (the prime orbit): if a prime cyclic
step `D` has `[D : E]` Mackey classes, then `D ⊆ E'` and two elements of
`Gal(L/E)` lie in the same double coset exactly when they agree on `D`. -/
theorem proposition48MackeyFibre : Proposition48MackeyFibreStatement.{uF} := by
  intro Q D _ hD hCard
  have : Normal Q.E Q.L := IsNormalClosure.normal (K := Q.E')
  have : IsGalois Q.E Q.L := ⟨⟩
  have : IsGalois Q.E D := hD.1
  have hHn : D.fixingSubgroup.Normal := IsGalois.fixingSubgroup_normal_of_isGalois D
  -- With `H = Gal(L/D)` normal, `a⁻¹ * b ∈ H` puts `a` and `b` in one double coset.
  have key : ∀ a b : Q.L ≃ₐ[Q.E] Q.L, a⁻¹ * b ∈ D.fixingSubgroup →
      DoubleCoset.mk D.fixingSubgroup (Q.conjugateField 1).fixingSubgroup a =
        DoubleCoset.mk D.fixingSubgroup (Q.conjugateField 1).fixingSubgroup b := by
    intro a b hab
    rw [DoubleCoset.eq]
    refine ⟨b * a⁻¹, ?_, 1, (Q.conjugateField 1).fixingSubgroup.one_mem, by group⟩
    convert hHn.conj_mem _ hab a using 1
    group
  -- The induced map `Gal(L/E) ⧸ H → Q.MackeyIndex D`.
  let f : (Q.L ≃ₐ[Q.E] Q.L) ⧸ D.fixingSubgroup → Q.MackeyIndex D :=
    Quotient.lift
      (fun a => DoubleCoset.mk D.fixingSubgroup (Q.conjugateField 1).fixingSubgroup a)
      (fun a b hab => key a b (QuotientGroup.leftRel_apply.mp hab))
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨a, rfl⟩ := Quotient.exists_rep q
    exact ⟨(a : (Q.L ≃ₐ[Q.E] Q.L) ⧸ D.fixingSubgroup), rfl⟩
  have hcardH : Nat.card ((Q.L ≃ₐ[Q.E] Q.L) ⧸ D.fixingSubgroup) = Module.finrank Q.E D :=
    (IntermediateField.finrank_eq_fixingSubgroup_index (L := D)).symm
  have hinj : Function.Injective f :=
    (hf.bijective_of_nat_card_le (by rw [hCard, hcardH])).1
  -- Injectivity gives `Gal(L/E') ≤ Gal(L/D)`.
  have hKH : (Q.conjugateField 1).fixingSubgroup ≤ D.fixingSubgroup := by
    intro k hk
    have h1 : f (k : (Q.L ≃ₐ[Q.E] Q.L) ⧸ D.fixingSubgroup) = f 1 := by
      change DoubleCoset.mk D.fixingSubgroup (Q.conjugateField 1).fixingSubgroup k =
        DoubleCoset.mk D.fixingSubgroup (Q.conjugateField 1).fixingSubgroup 1
      rw [DoubleCoset.eq]
      exact ⟨1, D.fixingSubgroup.one_mem, k⁻¹,
        (Q.conjugateField 1).fixingSubgroup.inv_mem hk, by group⟩
    exact (QuotientGroup.eq_one_iff k).mp (hinj h1)
  have hDle : D ≤ Q.conjugateField 1 := by
    rw [← IsGalois.fixedField_fixingSubgroup D,
      ← IsGalois.fixedField_fixingSubgroup (Q.conjugateField 1)]
    exact IntermediateField.fixedField_le hKH
  refine ⟨hDle, fun a b => ⟨fun hab x hx => ?_, fun hab => key a b ?_⟩⟩
  · rw [DoubleCoset.eq] at hab
    obtain ⟨h, hh, k, hk, rfl⟩ := hab
    have hmem : a⁻¹ * (h * a * k) ∈ D.fixingSubgroup := by
      have h1 : a⁻¹ * h * a ∈ D.fixingSubgroup := by
        simpa only [inv_inv] using hHn.conj_mem h hh a⁻¹
      have h2 : a⁻¹ * (h * a * k) = a⁻¹ * h * a * k := by group
      rw [h2]
      exact D.fixingSubgroup.mul_mem h1 (hKH hk)
    have h3 := (IntermediateField.mem_fixingSubgroup_iff D _).mp hmem x hx
    rw [AlgEquiv.mul_apply, AlgEquiv.aut_inv] at h3
    have h4 := congrArg a h3
    rw [AlgEquiv.apply_symm_apply] at h4
    exact h4.symm
  · rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    rw [AlgEquiv.mul_apply, AlgEquiv.aut_inv, ← hab x hx, AlgEquiv.symm_apply_apply]

end Langlands.Global.Harris
