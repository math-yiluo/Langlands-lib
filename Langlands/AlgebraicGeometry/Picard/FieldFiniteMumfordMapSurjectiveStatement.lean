import Langlands.AlgebraicGeometry.Picard.MumfordMap
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # A finite Mumford map to the chosen dual over a field is surjective -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

/-- Let `A` be an abelian scheme over a field `K` with chosen dual `D = dualScheme A hA`, and
let `f = mumfordSchemeMap preservation square A L M evaluation hA : A ⟶ D` be the actual Mumford
map of a rigidified line bundle `L` with inverse `M`. If the underlying scheme morphism of `f`
is finite, then it is surjective. This is Mumford's argument for the proof of Proposition
(7.21) of Edixhoven, van der Geer and Moonen, *Abelian Varieties*, with finiteness of `f` in
place of ampleness of `L`.
This definition states a proposition and does not prove it. -/
def FieldFiniteMumfordMapSurjectiveStatement : Prop :=
  ∀ (preservation : pullbackTensorComparisonIsIsoStatement.{u})
    (square : MumfordBundlePicardZeroStatement.{u})
    (K : Type u) [Field K]
    (A : AbelianScheme (Spec (CommRingCat.of K))) (hA : HasDualScheme A)
    (L : RigidifiedLineBundle (unitSection A)) (M : LineBundle A.X.left)
    (evaluation : tensorObj L.obj.carrier M.obj ≅ structureSheaf A.X.left),
    IsFinite (mumfordSchemeMap preservation square A L M evaluation hA).left →
      Function.Surjective (mumfordSchemeMap preservation square A L M evaluation hA).left

end Langlands.AbelianScheme
