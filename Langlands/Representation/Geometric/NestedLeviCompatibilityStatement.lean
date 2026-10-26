import Langlands.Representation.Geometric.FlattenedLevi

/-! # Parameters and actual inclusions through nested Levi refinements -/

noncomputable section

namespace Langlands

open GeneralLinear Geometric

universe uA uK

/-- Twice repeating a coarse parameter and twice including the actual fine Levi
agree with the direct refinement, under the literal fine-shape equality.
This proposition states the two compatibility laws without proving them. -/
def NestedLeviCompatibilityStatement : Prop :=
  (∀ (A : Type uA) (n : ℕ) (B : BlockShape n) (Q : BlockRefinement B)
      (R : BlockRefinement (B.flatten Q)) (S : BlockRefinement B)
      (h : (B.flatten Q).flatten R = B.flatten S) (a : Fin B.length → A),
    let aD : Fin (B.flatten Q).length → A :=
      fun j => a ((B.flattenBlockEquiv Q).symm j).1
    let aC : Fin ((B.flatten Q).flatten R).length → A :=
      fun k => aD (((B.flatten Q).flattenBlockEquiv R).symm k).1
    (h ▸ aC) = fun k => a ((B.flattenBlockEquiv S).symm k).1) ∧
  (∀ (K : Type uK) [CommRing K] (n : ℕ) (B : BlockShape n) (Q : BlockRefinement B)
      (R : BlockRefinement (B.flatten Q)) (S : BlockRefinement B)
      (h : (B.flatten Q).flatten R = B.flatten S)
      (m : ((B.flatten Q).flatten R).Levi K),
    (flattenedLeviEquiv K B S (h ▸ m)).val =
      (flattenedLeviEquiv K B Q
        (flattenedLeviEquiv K (B.flatten Q) R m).val).val)

end Langlands
