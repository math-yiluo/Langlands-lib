import Langlands.CategoryTheory.Renard.SmallProjective
import Mathlib.Data.Finset.Defs

/-!
# Small projectives and actual finite-subcoproduct factorization

This module states the characterization in Renard A.VIII.2. The finite subset
indexes an actual coproduct, and its canonical map to the full coproduct is
formed from the full coproduct injections. No characterization proof is supplied.
-/

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace Langlands.Renard

/-- Renard A.VIII.2: a projective object is small exactly when every morphism
to a coproduct factors through an actual finite subcoproduct. -/
def SmallProjectiveFiniteSupportStatement (C : Type u) [Category.{v} C] [Abelian C]
    [HasCoproducts.{w} C] : Prop :=
  ∀ P : C,
    HomSmallProjective.{w} P ↔
      HomProjective P ∧
        ∀ (I : Type w) (M : I → C) (φ : P ⟶ ∐ M),
          ∃ (s : Finset I) (g : P ⟶ ∐ (fun j : s => M j.val)),
            g ≫ Sigma.desc (fun j : s => Sigma.ι M j.val) = φ

end Langlands.Renard
