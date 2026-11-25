/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Extensive

/-!
# Trivial coverings in finitary extensive categories

A morphism `p : P ⟶ S` is a *trivial covering* if it has finitely many sections `t k` such that
the induced map `∐ₖ S ⟶ P` is an isomorphism. In a finitary pre-extensive category trivial
coverings are stable under base change: for a cartesian square

```
  P' --a--> P
  |         |
  p'        p
  v         v
  Y  --b--> S
```

the sections `(b ≫ t k, 𝟙)` of `p'` induce an isomorphism `∐ₖ Y ≅ P'`, finite coproducts being
universal.

## Main statements

- `CategoryTheory.FinitaryPreExtensive.isIso_sigmaDesc_isPullback_lift`.
-/

@[expose] public section

universe v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C]

/-- **Base change of a trivial covering.** Let `p : P ⟶ S` have finitely many sections `t k`
inducing an isomorphism `∐ₖ S ≅ P`, and let `P'` be the base change of `p` along `b : Y ⟶ S`.
Then the sections `(b ≫ t k, 𝟙)` of `p' : P' ⟶ Y` induce an isomorphism `∐ₖ Y ≅ P'`: the
cofan they form is the pullback of the coproduct cofan of the `t k` along `a : P' ⟶ P`, and finite
coproducts are universal. -/
lemma FinitaryPreExtensive.isIso_sigmaDesc_isPullback_lift [FinitaryPreExtensive C]
    {P S P' Y : C} {a : P' ⟶ P} {p' : P' ⟶ Y} {p : P ⟶ S} {b : Y ⟶ S}
    (h : IsPullback a p' p b) {κ : Type*} [Finite κ] (t : κ → (S ⟶ P))
    (ht : ∀ k, t k ≫ p = 𝟙 S) [HasCoproduct fun _ : κ ↦ S] [IsIso (Sigma.desc t)]
    [HasCoproduct fun _ : κ ↦ Y] :
    IsIso (Sigma.desc fun k ↦ h.lift (b ≫ t k) (𝟙 Y) (by simp [ht])) := by
  let c : Cofan (fun _ : κ ↦ S) := Cofan.mk _ t
  have : IsIso ((colimit.isColimit _).desc c) := ‹IsIso (Sigma.desc _)›
  have hc : IsColimit c := IsColimit.ofPointIso (colimit.isColimit _)
  let σ (k : κ) : Y ⟶ P' := h.lift (b ≫ t k) (𝟙 Y) (by simp [ht])
  let c' : Cofan (fun _ : κ ↦ Y) := Cofan.mk _ σ
  obtain ⟨hc'⟩ := FinitaryPreExtensive.isUniversal_finiteCoproducts hc c'
    (Discrete.natTrans fun _ ↦ b) a (by ext ⟨k⟩; simp [c, c', σ])
    (NatTrans.Equifibered.of_discrete _) fun ⟨k⟩ ↦ by
      refine IsPullback.of_right (h₁₂ := p') (h₂₂ := p) (v₁₃ := b) ?_ (by simp [c, c', σ])
        h.flip
      have h₁ : σ k ≫ p' = 𝟙 Y := h.lift_snd _ _ _
      simpa [c, c', h₁, ht] using IsPullback.of_id_fst (f := b)
  have : Sigma.desc σ = ((colimit.isColimit _).coconePointUniqueUpToIso hc').hom :=
    Sigma.hom_ext _ _ fun k ↦ by
      rw [colimit.ι_desc]
      exact ((colimit.isColimit _).comp_coconePointUniqueUpToIso_hom hc' ⟨k⟩).symm
  rw [this]
  infer_instance

end CategoryTheory
