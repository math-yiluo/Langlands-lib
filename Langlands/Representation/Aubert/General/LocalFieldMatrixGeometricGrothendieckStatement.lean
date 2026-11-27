import Langlands.AllField.Representation.CuspidalSupport.JacquetVanishingSmoothPieces
import Langlands.Representation.Smooth.FiniteLengthGrothendieck

/-! The actual matrix geometric lemma on finite-length Grothendieck classes. -/

namespace Langlands.Aubert.General.RationalPointFamily.GL

open GeneralLinear Geometric _root_.CategoryTheory

universe u v

/-- The actual normalized Jacquet restriction of an actual normalized induction
has the exact class sum of its geometric pieces, with a single choice of the
ordered intersections for all finite-length inputs. -/
def LocalFieldMatrixGeometricGrothendieckStatement : Prop :=
  ∀ (F : Type u) [Field F] (T : LocalFieldData F) (n : ℕ), 0 < n →
    ∀ B C : BlockShape n,
    letI := T.topology
    ∃ (S : MinimalRepresentatives B C → BlockRefinement B)
      (R : MinimalRepresentatives B C → BlockRefinement C),
    ∃ (hS : ∀ w, IsIntersectionRefinement (F := F) B C w.val (S w))
      (hR : ∀ w, IsIntersectionRefinement (F := F) C B w.val⁻¹ (R w)),
    ∃ (m : ℕ) (e : Fin m ≃ MinimalRepresentatives B C),
      ∀ (A : SmoothRep.{0, u, max (u + 1) v} ℂ (B.Levi F)) (_hA : A.HasFiniteLength),
        let J := T.normalizedParabolicInductionFunctor B ⋙ T.normalizedJacquetFunctor C
        let P (i : Fin m) := AllField.CuspidalSupport.geometricPieceSmoothFunctor F T B C
          (e i).val (S (e i)) (R (e i)) (hS (e i)).2.1 (hR (e i)).2.1
        ∃ (hJ : (J.obj A).HasFiniteLength) (hP : ∀ i, ((P i).obj A).HasFiniteLength),
          SmoothRep.FiniteLengthGrothendieckGroup.ofRepresentation (J.obj A) hJ =
            ∑ i : Fin m, SmoothRep.FiniteLengthGrothendieckGroup.ofRepresentation
              ((P i).obj A) (hP i)

end Langlands.Aubert.General.RationalPointFamily.GL
