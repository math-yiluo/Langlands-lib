/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Limits.FormalCoproducts.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
public import WeilConjectures.CategoryTheory.SimplicialMatchingObject

/-!
# Blueprint statements

corollary-cohomology-pro-etale-affine.
-/

@[expose] public section

universe w u

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

namespace AlgebraicGeometry.Scheme

/-- Required definitions for corollary-cohomology-pro-etale-affine. -/
noncomputable instance semiRepresentableHasFiniteLimits (X : Scheme.{u}) :
    HasFiniteLimits (FormalCoproduct.{w} X.Etale) :=
  hasFiniteLimits_of_hasTerminal_and_pullbacks

/-- Required definitions for corollary-cohomology-pro-etale-affine. -/
abbrev semiRepresentablePoints {X : Scheme.{u}} (T : X.Etale)
    (L : FormalCoproduct.{w} X.Etale) :=
  (FormalCoproduct.incl X.Etale).obj T ⟶ L

/-- Required definitions for corollary-cohomology-pro-etale-affine. -/
def semiRepresentablePointsMap {X : Scheme.{u}} (T : X.Etale)
    {L L' : FormalCoproduct.{w} X.Etale} (f : L ⟶ L') :
    semiRepresentablePoints T L → semiRepresentablePoints T L' :=
  fun t => t ≫ f

/-- Required definitions for corollary-cohomology-pro-etale-affine. -/
def IsSemiRepresentableCovering {X : Scheme.{u}}
    {U V : FormalCoproduct.{w} X.Etale} (f : U ⟶ V) : Prop :=
  ∀ j : V.I,
    Sieve.ofArrows (fun i : {i : U.I // f.f i = j} => U.obj i.val)
      (fun i => f.φ i.val ≫ eqToHom (congrArg V.obj i.property)) ∈
        X.smallEtaleTopology (V.obj j)

/-- Required definitions for corollary-cohomology-pro-etale-affine. -/
instance semiRepresentableHasMultiequalizer {X : Scheme.{u}}
    (K : SimplicialObject (FormalCoproduct.{w} X.Etale)) (n : ℕ) :
    HasMultiequalizer (SimplicialObject.matchingBoundaryIndex K n) := by
  have : Fintype (SimplicialObject.matchingBoundaryShape n).L :=
    inferInstanceAs (Fintype (Fin (n + 3)))
  have : Fintype (SimplicialObject.matchingBoundaryShape n).R :=
    inferInstanceAs (Fintype {p : Fin (n + 3) × Fin (n + 3) // p.1 < p.2})
  have : DecidableEq (SimplicialObject.matchingBoundaryShape n).L :=
    inferInstanceAs (DecidableEq (Fin (n + 3)))
  have : DecidableEq (SimplicialObject.matchingBoundaryShape n).R :=
    inferInstanceAs (DecidableEq {p : Fin (n + 3) × Fin (n + 3) // p.1 < p.2})
  infer_instance

/-- Required definitions for corollary-cohomology-pro-etale-affine. -/
noncomputable def semiRepresentableMatchingObject {X : Scheme.{u}}
    (K : SimplicialObject (FormalCoproduct.{w} X.Etale)) :
    ℕ → FormalCoproduct.{w} X.Etale
  | 0 => (FormalCoproduct.incl X.Etale).obj (Etale.mk (𝟙 X))
  | 1 => ∏ᶜ fun _ : Fin 2 => K _⦋0⦌
  | n + 2 => multiequalizer (SimplicialObject.matchingBoundaryIndex K n)

/-- Required definitions for corollary-cohomology-pro-etale-affine. -/
noncomputable def semiRepresentableMatchingMap {X : Scheme.{u}}
    (K : SimplicialObject (FormalCoproduct.{w} X.Etale)) :
    (n : ℕ) → K _⦋n⦌ ⟶ semiRepresentableMatchingObject K n
  | 0 => (FormalCoproduct.isTerminalIncl (Etale.mk (𝟙 X))
      ((Over.mkIdTerminal (X := X)).isTerminalOfObj (Etale.forget X) (Etale.mk (𝟙 X)))).from _
  | 1 => Pi.lift fun i : Fin 2 => K.δ i
  | n + 2 =>
      Multiequalizer.lift (SimplicialObject.matchingBoundaryIndex K n) _
        (fun i : Fin (n + 3) => K.δ i)
        (by
          rintro ⟨⟨a, b⟩, h⟩
          dsimp [SimplicialObject.matchingBoundaryIndex]
          have hb : b = (b.pred (Fin.ne_zero_of_lt h)).succ := (Fin.succ_pred _ _).symm
          have H : a.castLT (Nat.lt_of_lt_of_le h (Nat.le_of_lt_succ b.isLt)) ≤
              b.pred (Fin.ne_zero_of_lt h) := by
            rw [Fin.le_iff_val_le_val]
            have h' : a.val < b.val := h
            simp only [Fin.val_castLT, Fin.val_pred]
            omega
          have := (SimplicialObject.δ_comp_δ K H).symm
          rw [← hb] at this
          exact this)

/-- Required definitions for corollary-cohomology-pro-etale-affine. -/
def IsSemiRepresentableHypercover {X : Scheme.{u}}
    (K : SimplicialObject (FormalCoproduct.{w} X.Etale)) : Prop :=
  ∀ n : ℕ, IsSemiRepresentableCovering (semiRepresentableMatchingMap K n)

end AlgebraicGeometry.Scheme
