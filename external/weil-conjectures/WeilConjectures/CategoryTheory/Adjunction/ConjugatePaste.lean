/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Pasting exchange transformations of left adjoints through their conjugates

Consider three "stages" `A`, `B`, `C`, each over two "bases" `X`, `Y`, with base change functors
`u_A : A_X ⥤ A_Y`, `u_B`, `u_C` and change of stage functors `T : A ⥤ B`, `P : B ⥤ C`,
`Q : A ⥤ C` over each base, all of them left adjoints. Exchange transformations
`s_T : T_X ⋙ u_B ⟶ u_A ⋙ T_Y` (and `s_P`, `s_Q`) and comparisons `a : Q ⟶ T ⋙ P` satisfy the
pasting identity

```
u_C (Q_X M) ⟶ u_C (P_X (T_X M)) ⟶ P_Y (u_B (T_X M)) ⟶ P_Y (T_Y (u_A M))
  = u_C (Q_X M) ⟶ Q_Y (u_A M) ⟶ P_Y (T_Y (u_A M))
```

as soon as their conjugates, transformations between the right adjoints, satisfy the
corresponding identity (`CategoryTheory.conjugateEquiv_paste`). In applications the right
adjoints are restrictions of scalars and pushforwards, whose exchange transformations are
identities on the underlying objects, so that the identity between the conjugates is
immediate.
-/

@[expose] public section

namespace CategoryTheory

open CategoryTheory.Functor

variable {A₁ A₂ B₁ B₂ C₁ C₂ : Type*} [Category A₁] [Category A₂] [Category B₁] [Category B₂]
  [Category C₁] [Category C₂]

/-- The composite of adjunctions is associative. -/
lemma Adjunction.comp_assoc {D : Type*} [Category D] {F : A₁ ⥤ B₁} {G : B₁ ⥤ A₁}
    {F' : B₁ ⥤ C₁} {G' : C₁ ⥤ B₁} {F'' : C₁ ⥤ D} {G'' : D ⥤ C₁} (adj : F ⊣ G) (adj' : F' ⊣ G')
    (adj'' : F'' ⊣ G'') : (adj.comp adj').comp adj'' = adj.comp (adj'.comp adj'') := by
  ext X
  simp [Adjunction.comp]

variable {uA : A₁ ⥤ A₂} {dA : A₂ ⥤ A₁} {uB : B₁ ⥤ B₂} {dB : B₂ ⥤ B₁} {uC : C₁ ⥤ C₂}
  {dC : C₂ ⥤ C₁} (gA : uA ⊣ dA) (gB : uB ⊣ dB) (gC : uC ⊣ dC)
  {T₁ : A₁ ⥤ B₁} {RT₁ : B₁ ⥤ A₁} {T₂ : A₂ ⥤ B₂} {RT₂ : B₂ ⥤ A₂}
  {P₁ : B₁ ⥤ C₁} {RP₁ : C₁ ⥤ B₁} {P₂ : B₂ ⥤ C₂} {RP₂ : C₂ ⥤ B₂}
  {Q₁ : A₁ ⥤ C₁} {RQ₁ : C₁ ⥤ A₁} {Q₂ : A₂ ⥤ C₂} {RQ₂ : C₂ ⥤ A₂}
  (t₁ : T₁ ⊣ RT₁) (t₂ : T₂ ⊣ RT₂) (p₁ : P₁ ⊣ RP₁) (p₂ : P₂ ⊣ RP₂) (q₁ : Q₁ ⊣ RQ₁)
  (q₂ : Q₂ ⊣ RQ₂)

/-- **Pasting through conjugates.** The exchange transformations `s_T`, `s_P` and `s_Q` of the
left adjoints and the comparisons `a₁ : Q₁ ⟶ T₁ ⋙ P₁`, `a₂ : Q₂ ⟶ T₂ ⋙ P₂` satisfy the pasting
identity if their conjugates do. -/
lemma conjugateEquiv_paste (sT : T₁ ⋙ uB ⟶ uA ⋙ T₂) (sP : P₁ ⋙ uC ⟶ uB ⋙ P₂)
    (sQ : Q₁ ⋙ uC ⟶ uA ⋙ Q₂) (a₁ : Q₁ ⟶ T₁ ⋙ P₁) (a₂ : Q₂ ⟶ T₂ ⋙ P₂)
    (h : whiskerLeft RP₂ (conjugateEquiv (gA.comp t₂) (t₁.comp gB) sT) ≫
        whiskerRight (conjugateEquiv (gB.comp p₂) (p₁.comp gC) sP) RT₁ ≫
        whiskerLeft dC (conjugateEquiv (t₁.comp p₁) q₁ a₁) =
      whiskerRight (conjugateEquiv (t₂.comp p₂) q₂ a₂) dA ≫
        conjugateEquiv (gA.comp q₂) (q₁.comp gC) sQ) :
    whiskerRight a₁ uC ≫ whiskerLeft T₁ sP ≫ whiskerRight sT P₂ = sQ ≫ whiskerLeft uA a₂ := by
  have h₁ : conjugateEquiv (t₁.comp (p₁.comp gC)) (q₁.comp gC) (whiskerRight a₁ uC) =
      whiskerLeft dC (conjugateEquiv (t₁.comp p₁) q₁ a₁) := by
    rw [← Adjunction.comp_assoc]
    exact conjugateEquiv_whiskerRight (t₁.comp p₁) q₁ gC a₁
  have h₃ : conjugateEquiv (gA.comp (t₂.comp p₂)) (t₁.comp (gB.comp p₂)) (whiskerRight sT P₂) =
      whiskerLeft RP₂ (conjugateEquiv (gA.comp t₂) (t₁.comp gB) sT) := by
    rw [← Adjunction.comp_assoc, ← Adjunction.comp_assoc]
    exact conjugateEquiv_whiskerRight (gA.comp t₂) (t₁.comp gB) p₂ sT
  apply (conjugateEquiv (gA.comp (t₂.comp p₂)) (q₁.comp gC)).injective
  rw [← conjugateEquiv_comp (gA.comp (t₂.comp p₂)) (gA.comp q₂) (q₁.comp gC),
    conjugateEquiv_whiskerLeft, ← h,
    ← conjugateEquiv_comp (gA.comp (t₂.comp p₂)) (t₁.comp (p₁.comp gC)) (q₁.comp gC), h₁,
    ← conjugateEquiv_comp (gA.comp (t₂.comp p₂)) (t₁.comp (gB.comp p₂)) (t₁.comp (p₁.comp gC)),
    conjugateEquiv_whiskerLeft, h₃, Category.assoc]

section Cocycle

variable {A₃ A₄ : Type*} [Category A₃] [Category A₄]
  {L₁₂ : A₁ ⥤ A₂} {R₂₁ : A₂ ⥤ A₁} {L₂₃ : A₂ ⥤ A₃} {R₃₂ : A₃ ⥤ A₂} {L₃₄ : A₃ ⥤ A₄}
  {R₄₃ : A₄ ⥤ A₃} {L₁₃ : A₁ ⥤ A₃} {R₃₁ : A₃ ⥤ A₁} {L₂₄ : A₂ ⥤ A₄} {R₄₂ : A₄ ⥤ A₂}
  {L₁₄ : A₁ ⥤ A₄} {R₄₁ : A₄ ⥤ A₁} (t₁₂ : L₁₂ ⊣ R₂₁) (t₂₃ : L₂₃ ⊣ R₃₂) (t₃₄ : L₃₄ ⊣ R₄₃)
  (t₁₃ : L₁₃ ⊣ R₃₁) (t₂₄ : L₂₄ ⊣ R₄₂) (t₁₄ : L₁₄ ⊣ R₄₁)

/-- **The cocycle condition through conjugates.** Comparisons `a_{ijk} : L_{ik} ⟶ L_{ij} ⋙ L_{jk}`
of left adjoints satisfy the cocycle condition of an associator if their conjugates, the
comparisons `R_{kj} ⋙ R_{ji} ⟶ R_{ki}` of the right adjoints, do. -/
lemma conjugateEquiv_cocycle (a₁₂₃ : L₁₃ ⟶ L₁₂ ⋙ L₂₃) (a₁₃₄ : L₁₄ ⟶ L₁₃ ⋙ L₃₄)
    (a₂₃₄ : L₂₄ ⟶ L₂₃ ⋙ L₃₄) (a₁₂₄ : L₁₄ ⟶ L₁₂ ⋙ L₂₄)
    (h : whiskerLeft R₄₃ (conjugateEquiv (t₁₂.comp t₂₃) t₁₃ a₁₂₃) ≫
        conjugateEquiv (t₁₃.comp t₃₄) t₁₄ a₁₃₄ =
      whiskerRight (conjugateEquiv (t₂₃.comp t₃₄) t₂₄ a₂₃₄) R₂₁ ≫
        conjugateEquiv (t₁₂.comp t₂₄) t₁₄ a₁₂₄) :
    a₁₃₄ ≫ whiskerRight a₁₂₃ L₃₄ = a₁₂₄ ≫ whiskerLeft L₁₂ a₂₃₄ := by
  have h₁ : conjugateEquiv (t₁₂.comp (t₂₃.comp t₃₄)) (t₁₃.comp t₃₄) (whiskerRight a₁₂₃ L₃₄) =
      whiskerLeft R₄₃ (conjugateEquiv (t₁₂.comp t₂₃) t₁₃ a₁₂₃) := by
    rw [← Adjunction.comp_assoc]
    exact conjugateEquiv_whiskerRight (t₁₂.comp t₂₃) t₁₃ t₃₄ a₁₂₃
  apply (conjugateEquiv (t₁₂.comp (t₂₃.comp t₃₄)) t₁₄).injective
  rw [← conjugateEquiv_comp (t₁₂.comp (t₂₃.comp t₃₄)) (t₁₃.comp t₃₄) t₁₄, h₁, h,
    ← conjugateEquiv_comp (t₁₂.comp (t₂₃.comp t₃₄)) (t₁₂.comp t₂₄) t₁₄,
    conjugateEquiv_whiskerLeft]

end Cocycle

end CategoryTheory
