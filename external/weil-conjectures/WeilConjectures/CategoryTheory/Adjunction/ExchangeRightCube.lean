/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ExchangeRightPaste

/-!

# The cube law of exchange morphisms

Consider two adjunctions `Lf ⊣ Rf` (between `B` and `A`) and `Lf' ⊣ Rf'` (between `B'` and `A'`),
functors `G_A`, `G_B` on `A`, `B`, functors `P_A : A ⥤ A'`, `P_B : B ⥤ B'` and `Φ_A`, `Φ_B` on
`A'`, `B'`, with comparisons `θ_e : G_B ⋙ Lf ≅ Lf ⋙ G_A`, `θ_π : P_B ⋙ Lf' ≅ Lf ⋙ P_A`,
`θ_Φ : Φ_B ⋙ Lf' ≅ Lf' ⋙ Φ_A` of left adjoints, and isomorphisms `c_A : P_A ⋙ Φ_A ≅ G_A ⋙ P_A`,
`c_B : P_B ⋙ Φ_B ≅ G_B ⋙ P_B`. If the comparisons of left adjoints form a commutative cube with
`c_A`, `c_B`, then so do the exchange morphisms of the right adjoints
(`CategoryTheory.Adjunction.exchangeRight_app_cube`): this is two applications of the pasting law
`CategoryTheory.Adjunction.exchangeRight_app_paste`, for the pastings of `θ_e`, `θ_π` and of
`θ_π`, `θ_Φ`.

In the applications, `Lf`, `Lf'` are derived pullbacks along a morphism `f` and its base change
`f̄`, `G` and `Φ` are pullbacks along Frobenius endomorphisms and `P` the pullbacks along the base
change: the cube law says that the base change morphism along `P` of the direct images intertwines
the Frobenius structures.

-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Adjunction

variable {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
  {Lf : B ⥤ A} {Rf : A ⥤ B} {Lf' : B' ⥤ A'} {Rf' : A' ⥤ B'}
  {GA : A ⥤ A} {GB : B ⥤ B} {PA : A ⥤ A'} {PB : B ⥤ B'} {ΦA : A' ⥤ A'} {ΦB : B' ⥤ B'}

/-- The pasting `(P_B ⋙ Φ_B) ⋙ Lf' ≅ Lf ⋙ (P_A ⋙ Φ_A)` of comparisons
`θ_π : P_B ⋙ Lf' ≅ Lf ⋙ P_A` and `θ_Φ : Φ_B ⋙ Lf' ≅ Lf' ⋙ Φ_A`. -/
def pasteIso (θπ : PB ⋙ Lf' ≅ Lf ⋙ PA) (θΦ : ΦB ⋙ Lf' ≅ Lf' ⋙ ΦA) :
    (PB ⋙ ΦB) ⋙ Lf' ≅ Lf ⋙ (PA ⋙ ΦA) :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft PB θΦ ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight θπ ΦA ≪≫ Functor.associator _ _ _

@[simp]
lemma pasteIso_hom_app (θπ : PB ⋙ Lf' ≅ Lf ⋙ PA) (θΦ : ΦB ⋙ Lf' ≅ Lf' ⋙ ΦA) (N : B) :
    (pasteIso θπ θΦ).hom.app N = θΦ.hom.app (PB.obj N) ≫ ΦA.map (θπ.hom.app N) := by
  simp [pasteIso]

/-- The *cube condition* on comparisons of left adjoints: `θ_e`, `θ_π`, `θ_Φ` commute with
`c_A : P_A ⋙ Φ_A ≅ G_A ⋙ P_A` and `c_B : P_B ⋙ Φ_B ≅ G_B ⋙ P_B`. -/
def CubeCondition (θe : GB ⋙ Lf ≅ Lf ⋙ GA) (θπ : PB ⋙ Lf' ≅ Lf ⋙ PA)
    (θΦ : ΦB ⋙ Lf' ≅ Lf' ⋙ ΦA) (cA : PA ⋙ ΦA ≅ GA ⋙ PA) (cB : PB ⋙ ΦB ≅ GB ⋙ PB) : Prop :=
  ∀ N : B, Lf'.map (cB.hom.app N) ≫ θπ.hom.app (GB.obj N) ≫ PA.map (θe.hom.app N) =
    θΦ.hom.app (PB.obj N) ≫ ΦA.map (θπ.hom.app N) ≫ cA.hom.app (Lf.obj N)

/-- **The cube law of exchange morphisms.** If the comparisons `θ_e`, `θ_π`, `θ_Φ` of left
adjoints commute with `c_A : P_A ⋙ Φ_A ≅ G_A ⋙ P_A` and `c_B : P_B ⋙ Φ_B ≅ G_B ⋙ P_B`, then
so do the exchange morphisms of the right adjoints:
```
Φ_B P_B Rf K --Φ_B(Ex_π)--> Φ_B Rf' P_A K --Ex_Φ--> Rf' Φ_A P_A K --Rf'(c_A)--> Rf' P_A G_A K
     ‖                                                                              ‖
Φ_B P_B Rf K --c_B--> P_B G_B Rf K --P_B(Ex_e)--> P_B Rf G_A K --Ex_π-------> Rf' P_A G_A K
```
-/
lemma exchangeRight_app_cube (af : Lf ⊣ Rf) (af' : Lf' ⊣ Rf') (θe : GB ⋙ Lf ≅ Lf ⋙ GA)
    (θπ : PB ⋙ Lf' ≅ Lf ⋙ PA) (θΦ : ΦB ⋙ Lf' ≅ Lf' ⋙ ΦA) (cA : PA ⋙ ΦA ≅ GA ⋙ PA)
    (cB : PB ⋙ ΦB ≅ GB ⋙ PB)
    (h : CubeCondition θe θπ θΦ cA cB) (K : A) :
    ΦB.map ((exchangeRight af af' θπ).app K) ≫ (exchangeRight af' af' θΦ).app (PA.obj K) ≫
        Rf'.map (cA.hom.app K) =
      cB.hom.app (Rf.obj K) ≫ PB.map ((exchangeRight af af θe).app K) ≫
        (exchangeRight af af' θπ).app (GA.obj K) := by
  have h₁ := exchangeRight_app_paste af af' af' θπ θΦ (pasteIso θπ θΦ) (Iso.refl _) (Iso.refl _)
    (fun N ↦ by simp) K
  have h₂ := exchangeRight_app_paste af af af' θe θπ (pasteIso θπ θΦ) cB cA
    (fun N ↦ by rw [h N, pasteIso_hom_app, Category.assoc]) K
  simp only [Iso.refl_hom, NatTrans.id_app, Functor.map_id, Category.id_comp] at h₁
  erw [Category.comp_id] at h₁
  rw [h₂, ← h₁, Category.assoc]

end CategoryTheory.Adjunction
