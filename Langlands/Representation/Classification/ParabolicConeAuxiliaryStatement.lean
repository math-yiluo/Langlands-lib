import Langlands.Representation.Classification.ParabolicConeStatement

/-! Internal interfaces separating the numerical cone problem from its matrix realization. -/

namespace Langlands

open GeneralLinear
open scoped BigOperators

universe uR

/-- The numerical conditions of the block root/weight cone decomposition. -/
def GLBlockConeNumericalConditions {n : ℕ} (B C : BlockShape n)
    (r : Fin B.length → ℝ) (q : Fin B.length → Fin C.length)
    (t : Fin C.length → ℝ) : Prop :=
  Monotone q ∧ Function.Surjective q ∧
  (∀ j, C.size j = ∑ i ∈ Finset.univ.filter (fun i => q i = j), B.size i) ∧
  StrictAnti t ∧
  (∀ j, (∑ i ∈ Finset.univ.filter (fun i => q i = j), r i) =
    (C.size j : ℝ) * t j) ∧
  (∀ i, (∑ k ∈ Finset.univ.filter (fun k => q k = q i ∧ k ≤ i),
    (r k - (B.size k : ℝ) * t (q i))) ≤ 0)

/-- Numerical cone existence, including the zero-rank empty shape. -/
def GLBlockConeExistenceStatement : Prop :=
  ∀ (n : ℕ) (B : BlockShape n) (r : Fin B.length → ℝ),
    ∃ (C : BlockShape n) (q : Fin B.length → Fin C.length) (t : Fin C.length → ℝ),
      GLBlockConeNumericalConditions B C r q t

/-- The numerical conditions alone determine the actual ordered coarse shape. -/
def GLBlockConeUniquenessStatement : Prop :=
  ∀ (n : ℕ) (B : BlockShape n) (r : Fin B.length → ℝ)
    (C D : BlockShape n)
    (q : Fin B.length → Fin C.length) (t : Fin C.length → ℝ)
    (q' : Fin B.length → Fin D.length) (t' : Fin D.length → ℝ),
    GLBlockConeNumericalConditions B C r q t →
    GLBlockConeNumericalConditions B D r q' t' → C = D

/-- Consecutive fiber-size coarsenings contain the fine parabolic and Levi. -/
def GLBlockCoarseningSubgroupStatement : Prop :=
  ∀ (n : ℕ) (B C : BlockShape n) (q : Fin B.length → Fin C.length),
    Monotone q → Function.Surjective q →
    (∀ j, C.size j = ∑ i ∈ Finset.univ.filter (fun i => q i = j), B.size i) →
    ∀ (R : Type uR) [CommRing R],
      B.parabolic R ≤ C.parabolic R ∧ B.leviSubgroup R ≤ C.leviSubgroup R

/-- The three independent interfaces used to assemble the block cone theorem. -/
def GLBlockConeAuxiliaryStatements : Prop :=
  GLBlockConeExistenceStatement ∧ GLBlockConeUniquenessStatement ∧
    GLBlockCoarseningSubgroupStatement.{uR}

end Langlands
