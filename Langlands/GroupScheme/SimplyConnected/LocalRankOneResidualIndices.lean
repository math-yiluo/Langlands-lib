import Langlands.GroupScheme.SimplyConnected.LocalRankOneTitsIndexStatement

/-! # Three residual patterns of actual rank-one indices -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.TitsIndexData

variable {K : Type u} [Field K]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (d : TitsIndexData G)

/-- A type-B diagram of rank at least three, with exactly one of its final
two vertices distinguished and with trivial full star action. -/
def HasRankOneHigherBIndex : Prop :=
  ∃ n : ℕ, 3 ≤ n ∧
    (∃ (e : d.Vertex ≃ Fin n) (j : Fin n),
      (j.val + 2 = n ∨ j.val + 1 = n) ∧
        d.IsNumberingOf (CartanMatrix.B n) (fun i => i = j) e) ∧
    d.StarIsTrivial

/-- A type-G2 diagram with precisely its long-root vertex distinguished
and with trivial full star action. -/
def HasRankOneG2Index : Prop :=
  (∃ e : d.Vertex ≃ Fin 2,
    d.IsNumberingOf CartanMatrix.G₂ (fun i => i.val = 0) e) ∧
    d.StarIsTrivial

/-- A centrally marked type-D4 diagram whose full star action is trivial
or has no globally fixed leaf. -/
def HasRankOneD4InnerOrNoFixedLeafIndex : Prop :=
  ∃ e : d.Vertex ≃ Fin 4,
    d.IsNumberingOf (CartanMatrix.D 4) (fun i => i.val = 1) e ∧
      (d.StarIsTrivial ∨
        ¬ ∃ a : d.Vertex, e a ≠ 1 ∧
          ∀ σ : SeparableClosure K ≃ₐ[K] SeparableClosure K, d.star σ a = a)

/-- The three explicitly specified residual patterns after the classical
index reductions and the conditional exceptional exclusions. -/
def HasResidualRankOneIndex : Prop :=
  d.HasRankOneHigherBIndex ∨ d.HasRankOneG2Index ∨
    d.HasRankOneD4InnerOrNoFixedLeafIndex

end Langlands.GroupScheme.TitsIndexData
