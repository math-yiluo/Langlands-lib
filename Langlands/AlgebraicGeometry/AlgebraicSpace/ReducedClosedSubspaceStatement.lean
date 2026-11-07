import Langlands.AlgebraicGeometry.AlgebraicSpace.SameImagePoints
import Langlands.AlgebraicGeometry.AlgebraicSpace.FiniteSurjectiveQuasiAffineSourceAFStatement

/-! # Algebraic spaces under saturated reduced closed subschemes of a finite cover

Let `f : U ⟶ Y` be a finite surjective map from a scheme to a quasi-compact quasi-separated
algebraic space. A reduced closed subscheme `U_T` of `U` whose underlying set is saturated for
`f` is again a finite surjective cover of an algebraic space, with the same identifications of
points as in `Y`. The algebraic space is the reduced closed subspace of `Y` on the image of `U_T`.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- Let `f : U ⟶ Y` be finite and surjective, `Y` quasi-compact and quasi-separated, and let
`j : U_T ⟶ U` be a closed immersion from a reduced scheme whose range is saturated: a point with
the same image under `f` as a point of the range lies in the range. Then there are a
quasi-compact quasi-separated algebraic space `Y_T` and a finite surjective map
`f_T : U_T ⟶ Y_T` such that two points of `U_T` have the same image under `f_T` exactly when
their images in `U` have the same image under `f`. -/
def ReducedClosedSubspaceStatement : Prop :=
  ∀ (S : Scheme.{u}) (U : Over S) (Y : AlgebraicSpace S) (f : (schemeToSpace S).obj U ⟶ Y),
    IsQuasiCompact Y → IsQuasiSeparated Y → IsFinite (hom f) → IsSurjective (hom f) →
      ∀ (UT : Over S) (j : UT ⟶ U), _root_.AlgebraicGeometry.IsClosedImmersion j.left →
        _root_.AlgebraicGeometry.IsReduced UT.left →
        (∀ u u', SameImage (hom f) u u' → u ∈ Set.range j.left → u' ∈ Set.range j.left) →
          ∃ (YT : AlgebraicSpace S) (fT : (schemeToSpace S).obj UT ⟶ YT),
            IsQuasiCompact YT ∧ IsQuasiSeparated YT ∧ IsFinite (hom fT) ∧
              IsSurjective (hom fT) ∧
                ∀ x x' : UT.left,
                  SameImage (hom fT) x x' ↔ SameImage (hom f) (j.left x) (j.left x')

end Langlands.AlgebraicGeometry.AlgebraicSpace
