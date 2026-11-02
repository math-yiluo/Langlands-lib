import Langlands.AlgebraicGeometry.Picard.MumfordLineBundle
import Langlands.AlgebraicGeometry.Modules.EulerCharacteristic
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # The dual-side Euler characteristic of a finite flat Mumford map -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.Modules.DerivedSections

/-- On an abelian scheme of relative dimension `g` over an algebraically closed field, if the
actual Mumford map `f` of a normalized line bundle `N` with inverse `M` is finite and flat, then
the Euler characteristic of `m^* N ⊗ snd^* M` on the parameter-first self-product is `(-1)^g`
times the native degree of `f` at every point of the chosen dual
(Edixhoven–van der Geer–Moonen, proof of (9.11), formulas (8)–(10)).
This proposition is a statement target, not a proof. -/
def AlgClosedFieldMumfordDualEulerStatement : Prop :=
  ∀ (preservation : pullbackTensorComparisonIsIsoStatement.{u})
    (square : MumfordBundlePicardZeroStatement.{u})
    (K : Type u) [Field K] [IsAlgClosed K]
    (A : AbelianScheme (Spec (CommRingCat.of K))) (hA : HasDualScheme A)
    (L : LineBundle A.X.left)
    (B : LineBundle (Spec (CommRingCat.of K)))
    (evaluationB : tensorObj ((Scheme.Modules.pullback (unitSection A)).obj L.obj) B.obj ≅
      structureSheaf (Spec (CommRingCat.of K)))
    (M : LineBundle A.X.left)
    (evaluation : tensorObj (LineBundle.normalize preservation A.X.hom (unitSection A)
      (unitSection_comp A) L B evaluationB).obj.carrier M.obj ≅ structureSheaf A.X.left)
    (f : A.X ⟶ dualScheme A hA),
    f = mumfordSchemeMapOfLineBundle preservation A L B evaluationB M evaluation square hA →
      IsFinite f.left → Flat f.left →
    ∀ (g : ℕ), A.HasRelativeDimension g →
    ∀ (hQ : HasFiniteCohomology (mumfordProduct A).hom
        (tensorObj
          ((Scheme.Modules.pullback (mumfordAddition A)).obj
            (LineBundle.normalize preservation A.X.hom (unitSection A)
              (unitSection_comp A) L B evaluationB).obj.carrier)
          ((Scheme.Modules.pullback (Limits.pullback.snd A.X.hom A.X.hom)).obj M.obj)))
      (y : (dualScheme A hA).left),
      eulerCharacteristic (mumfordProduct A).hom
          (tensorObj
            ((Scheme.Modules.pullback (mumfordAddition A)).obj
              (LineBundle.normalize preservation A.X.hom (unitSection A)
                (unitSection_comp A) L B evaluationB).obj.carrier)
            ((Scheme.Modules.pullback (Limits.pullback.snd A.X.hom A.X.hom)).obj M.obj)) hQ =
        (-1) ^ g * (f.left.finrank y : ℤ)

end Langlands.AbelianScheme
