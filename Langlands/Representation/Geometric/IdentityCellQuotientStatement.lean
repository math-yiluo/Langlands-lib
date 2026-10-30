import Langlands.Representation.Geometric.GeometricLemmaStatement

/-! The identity-cell quotient of the normalized geometric lemma (Ze80 1.3). -/

namespace Langlands.Geometric

open GeneralLinear CategoryTheory

universe uF uV

/-- For the identity permutation, with any standard intersection refinements,
there is a natural transformation from the normalized Jacquet module of the
normalized induced representation onto the identity geometric piece, whose
components are all surjective. -/
def PadicIdentityCellQuotientTheorem : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (n : ℕ), 0 < n → ∀ B C : BlockShape n,
    ∀ (S : BlockRefinement B) (R : BlockRefinement C)
      (hS : IsIntersectionRefinement (F := F.Carrier) B C 1 S)
      (hR : IsIntersectionRefinement (F := F.Carrier) C B 1⁻¹ R),
      ∃ η : jacquetInductionFunctor.{uF, uV} T B C ⟶
          geometricPieceFunctor T B C 1 S R hS.2.1 hR.2.1,
        ∀ A, Function.Surjective (η.app A).hom

end Langlands.Geometric
