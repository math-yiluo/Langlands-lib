/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import WeilConjectures.CategoryTheory.Monoidal.Mod.EvaluationPairing
public import WeilConjectures.CategoryTheory.Monoidal.Mod.Transpose

/-!
# The pairing induced by a transpose

Let `Φ : C ⥤ ModuleCat R` be a lax braided functor. For the transpose
`CategoryTheory.Mod.transpose v : M ⟶ Hom_A(P, N)` of `v : P ⟶ Hom_A(M, N)`, the pairings
`Φ Hom_A(-, N) × Φ (-) → Φ N` induced by the evaluations satisfy
`⟨Φ (transpose v) m, p⟩ = ⟨Φ v p, m⟩` (`CategoryTheory.Mod.evaluationPairing_transpose`).
-/

@[expose] public section

universe w v u

open CategoryTheory MonoidalCategory Limits Functor.LaxMonoidal

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] {A : C} [MonObj A]
  [SymmetricCategory C] [IsCommMonObj A] [Abelian C] [MonoidalPreadditive C]
  [IsGrothendieckAbelian.{v} C]
  [∀ X : C, PreservesColimitsOfSize.{v, v} (MonoidalCategory.tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{v, v} (MonoidalCategory.tensorRight X)]
  {R : Type w} [CommRing R] (Φ : C ⥤ ModuleCat.{w} R) [Φ.LaxBraided]

/-- The pairing induced by the transpose `M ⟶ Hom_A(P, N)` of `v : P ⟶ Hom_A(M, N)` is the
pairing of `v` with the arguments exchanged. -/
lemma evaluationPairing_transpose {P M N : Mod C A} (v : P ⟶ (ihom M).obj N)
    (m : Φ.obj M.X) (p : Φ.obj P.X) :
    evaluationPairing Φ P N ((Φ.map (transpose v).hom).hom m) p =
      evaluationPairing Φ M N ((Φ.map v.hom).hom p) m := by
  have hT := uncurryHom_transpose v
  rw [uncurryHom, uncurryHom] at hT
  have h : Φ.map (transpose v).hom ▷ Φ.obj P.X ≫ μ Φ _ _ ≫ Φ.map (evaluation P N) =
      (β_ (Φ.obj M.X) (Φ.obj P.X)).hom ≫ Φ.map v.hom ▷ Φ.obj M.X ≫ μ Φ _ _ ≫
        Φ.map (evaluation M N) := by
    rw [μ_natural_left_assoc, ← Φ.map_comp, hT, Φ.map_comp, Functor.LaxBraided.braided_assoc,
      Φ.map_comp, μ_natural_left_assoc]
  exact congrArg (fun f ↦ f.hom (m ⊗ₜ p)) h

end CategoryTheory.Mod
