import Langlands.AlgebraicGeometry.Picard.SquareTheorem

/-! # Symmetry of Poincaré slices at a point -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

variable {S : Scheme.{u}} (A : AbelianScheme S) (hA : HasDualScheme A)

/-- For `f : A ⟶ A^∨` and a point `t : T ⟶ A`, the two slices of the Poincaré family
through `t` agree on `T ×_S A`: the pullbacks of `P` along `(τ, a) ↦ (f τ, a)` and
`(τ, a) ↦ (f a, t τ)`, with `τ` the parameter coordinate and `a` the coordinate on `A`,
are isomorphic as line bundles. -/
def PoincareSliceSymmetric (f : A.X ⟶ dualScheme A hA) {T : Over S} (t : T ⟶ A.X) : Prop :=
  Nonempty ((LineBundle.pullback
      (pairOver A (relativeFst A T ≫ t ≫ f) (relativeSnd A T)).left).obj
        ((RigidifiedLineBundle.forget _).obj (poincareFamily A hA)) ≅
    (LineBundle.pullback (pairOver A (relativeSnd A T ≫ f) (relativeFst A T ≫ t)).left).obj
        ((RigidifiedLineBundle.forget _).obj (poincareFamily A hA)))

end Langlands.AbelianScheme
