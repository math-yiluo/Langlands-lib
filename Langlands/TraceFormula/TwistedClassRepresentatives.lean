import Langlands.TraceFormula.TwistedOrbital

/-!
# Finitely many twisted classes from a finite-valued separating map

`exists_twistedClass_representatives`: if a map `c` sends a set `S` of points of a subgroup
`Γ` into a finite set and identifies only points of `S` that are `θ`-twisted-conjugate under
`Γ`, then there are finitely many points of `S`, pairwise not twisted-conjugate, representing
every point of `S`. It chooses one point in each twisted class of `S`; the classes inject into
the finite set.
-/

noncomputable section

namespace Langlands.TraceFormula

section Representatives

variable {H : Type*} [Group H] {E : Type*} [FunLike E H H] [MonoidHomClass E H H]

private theorem isTwistedConjugate_refl' (Γ : Subgroup H) (θ : E) (x : H) :
    IsTwistedConjugate Γ θ x x :=
  ⟨1, Γ.one_mem, by simp⟩

private theorem isTwistedConjugate_symm' {Γ : Subgroup H} {θ : E} {x y : H}
    (h : IsTwistedConjugate Γ θ x y) : IsTwistedConjugate Γ θ y x := by
  obtain ⟨g, hg, rfl⟩ := h
  refine ⟨g⁻¹, Γ.inv_mem hg, ?_⟩
  simp only [inv_inv, map_inv]
  group

private theorem isTwistedConjugate_trans' {Γ : Subgroup H} {θ : E} {x y z : H}
    (h₁ : IsTwistedConjugate Γ θ x y) (h₂ : IsTwistedConjugate Γ θ y z) :
    IsTwistedConjugate Γ θ x z := by
  obtain ⟨g, hg, rfl⟩ := h₁
  obtain ⟨k, hk, rfl⟩ := h₂
  refine ⟨g * k, Γ.mul_mem hg hk, ?_⟩
  simp only [mul_inv_rev, map_mul]
  group

/-- If a map `c` sends a set `S` of points of `Γ` into a finite set and identifies only
`Γ`-twisted-conjugate points of `S`, then `S` meets finitely many twisted classes: there are
finitely many points of `S`, pairwise not twisted-conjugate, representing every point of
`S`. -/
theorem exists_twistedClass_representatives (Γ : Subgroup H) (θ : E) (S : Set Γ)
    {R : Type*} (c : Γ → R) (Rs : Set R) (hRs : Rs.Finite) (hcR : ∀ q ∈ S, c q ∈ Rs)
    (hc : ∀ q ∈ S, ∀ q' ∈ S, c q = c q' → IsTwistedConjugate Γ θ (q : H) (q' : H)) :
    ∃ (m : ℕ) (r : Fin m → Γ), (∀ j, r j ∈ S) ∧
      (∀ j k, IsTwistedConjugate Γ θ (r j : H) (r k : H) → j = k) ∧
      ∀ q ∈ S, ∃ j, IsTwistedConjugate Γ θ (r j : H) (q : H) := by
  classical
  let s : Setoid S :=
    { r := fun a b => IsTwistedConjugate Γ θ ((a : Γ) : H) ((b : Γ) : H)
      iseqv := ⟨fun a => isTwistedConjugate_refl' Γ θ _, isTwistedConjugate_symm',
        isTwistedConjugate_trans'⟩ }
  let Q := Quotient s
  let g : Q → Rs := fun a => ⟨c (Quotient.out a : S), hcR _ (Quotient.out a).property⟩
  have hg : Function.Injective g := by
    intro a b hab
    rw [← Quotient.out_eq a, ← Quotient.out_eq b]
    exact Quotient.sound (hc _ (Quotient.out a).property _ (Quotient.out b).property
      (congrArg Subtype.val hab))
  have : Finite Rs := hRs.to_subtype
  have : Finite Q := Finite.of_injective g hg
  let eQ := Finite.equivFin Q
  refine ⟨Nat.card Q, fun j => (Quotient.out (eQ.symm j) : S), fun j =>
    (Quotient.out (eQ.symm j)).property, ?_, ?_⟩
  · intro j k hjk
    apply eQ.symm.injective
    rw [← Quotient.out_eq (eQ.symm j), ← Quotient.out_eq (eQ.symm k)]
    exact Quotient.sound hjk
  · intro q hq
    refine ⟨eQ (Quotient.mk s ⟨q, hq⟩), ?_⟩
    change IsTwistedConjugate Γ θ ((Quotient.out (eQ.symm (eQ (Quotient.mk s ⟨q, hq⟩))) : S) :
      H) _
    rw [Equiv.symm_apply_apply]
    exact Quotient.mk_out (s := s) ⟨q, hq⟩

end Representatives

end Langlands.TraceFormula
