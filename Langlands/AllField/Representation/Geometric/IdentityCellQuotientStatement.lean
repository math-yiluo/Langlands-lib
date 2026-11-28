import Langlands.AllField.Representation.Geometric.GeometricLemmaStatement

/-! The identity-cell quotient for actual normalized parabolic functors. -/

namespace Langlands.AllField.Geometric

open CategoryTheory Langlands.GeneralLinear
open Langlands.Geometric (BlockRefinement IsIntersectionRefinement)

universe uF uV

/-- The normalized induction-Jacquet composite maps naturally and
objectwise surjectively onto the piece of the identity minimal representative. -/
def IdentityCellQuotientStatement : Prop :=
  ∀ (F : Type uF) [Field F] (T : LocalFieldData F)
    (n : ℕ), 0 < n → ∀ (B C : BlockShape n)
    (S : BlockRefinement B) (R : BlockRefinement C)
    (hS : IsIntersectionRefinement (F := F) B C 1 S)
    (hR : IsIntersectionRefinement (F := F) C B 1⁻¹ R),
    ∃ η : jacquetInductionFunctor.{uF,uV} T B C ⟶
      geometricPieceFunctor T B C 1 S R hS.2.1 hR.2.1,
      ∀ A, Function.Surjective (η.app A).hom

end Langlands.AllField.Geometric
