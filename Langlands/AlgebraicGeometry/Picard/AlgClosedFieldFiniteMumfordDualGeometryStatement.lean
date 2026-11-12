import Langlands.AlgebraicGeometry.Picard.MumfordMap
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # The chosen dual under a finite flat Mumford map over an algebraically closed field -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

/-- Let `A` be an abelian scheme over an algebraically closed field `K` with chosen dual
`D = dualScheme A hA`, and let `f = mumfordSchemeMap preservation square A L M evaluation hA`
be the actual Mumford map of a rigidified line bundle `L` with inverse `M`. If the underlying
scheme morphism of `f` is finite and flat, then its degree `f.left.finrank y` is the same at
all points `y` of `D`, and `D ⟶ Spec K` is smooth of relative dimension `g` whenever `A` is.
Compare Theorem (6.18) of Edixhoven, van der Geer and Moonen, *Abelian Varieties*.
This definition states a proposition and does not prove it. -/
def AlgClosedFieldFiniteMumfordDualGeometryStatement : Prop :=
  ∀ (preservation : pullbackTensorComparisonIsIsoStatement.{u})
    (square : MumfordBundlePicardZeroStatement.{u})
    (K : Type u) [Field K] [IsAlgClosed K]
    (A : AbelianScheme (Spec (CommRingCat.of K))) (hA : HasDualScheme A)
    (L : RigidifiedLineBundle (unitSection A)) (M : LineBundle A.X.left)
    (evaluation : tensorObj L.obj.carrier M.obj ≅ structureSheaf A.X.left),
    IsFinite (mumfordSchemeMap preservation square A L M evaluation hA).left →
    Flat (mumfordSchemeMap preservation square A L M evaluation hA).left →
      (∀ y y' : (dualScheme A hA).left,
        (mumfordSchemeMap preservation square A L M evaluation hA).left.finrank y =
          (mumfordSchemeMap preservation square A L M evaluation hA).left.finrank y') ∧
      ∀ g : ℕ, A.HasRelativeDimension g → SmoothOfRelativeDimension g (dualScheme A hA).hom

end Langlands.AbelianScheme
