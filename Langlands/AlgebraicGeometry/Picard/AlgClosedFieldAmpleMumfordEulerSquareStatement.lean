import Langlands.AlgebraicGeometry.Picard.Ample
import Langlands.AlgebraicGeometry.Picard.MumfordLineBundle
import Langlands.AlgebraicGeometry.Modules.EulerCharacteristic
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # The Euler-characteristic square formula for the Mumford map of an ample line bundle -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.Modules.DerivedSections

/-- On an abelian scheme over an algebraically closed field, the square of the Euler
characteristic of an ample line bundle `L` equals the native degree, at every point of the
chosen dual, of the actual Mumford map of `L`, provided that map is finite and flat
(Milne, Theorem 13.3 (a); GIT, Proposition 6.13 (iii)).
This proposition is a statement target, not a proof. -/
def AlgClosedFieldAmpleMumfordEulerSquareStatement : Prop :=
  ∀ (preservation : pullbackTensorComparisonIsIsoStatement.{u})
    (square : MumfordBundlePicardZeroStatement.{u})
    (K : Type u) [Field K] [IsAlgClosed K]
    (A : AbelianScheme (Spec (CommRingCat.of K))) (hA : HasDualScheme A)
    (L : LineBundle A.X.left), L.IsAmple →
    ∀ (h : HasFiniteCohomology A.X.hom L.obj)
      (B : LineBundle (Spec (CommRingCat.of K)))
      (evaluationB : tensorObj ((Scheme.Modules.pullback (unitSection A)).obj L.obj) B.obj ≅
        structureSheaf (Spec (CommRingCat.of K)))
      (M : LineBundle A.X.left)
      (evaluation : tensorObj (LineBundle.normalize preservation A.X.hom (unitSection A)
        (unitSection_comp A) L B evaluationB).obj.carrier M.obj ≅ structureSheaf A.X.left)
      (f : A.X ⟶ dualScheme A hA),
      f = mumfordSchemeMapOfLineBundle preservation A L B evaluationB M evaluation square hA →
        IsFinite f.left → Flat f.left →
          ∀ y : (dualScheme A hA).left,
            eulerCharacteristic A.X.hom L.obj h ^ 2 = (f.left.finrank y : ℤ)

end Langlands.AbelianScheme
