import Langlands.AlgebraicGeometry.Picard.DualScheme
import Langlands.AlgebraicGeometry.Picard.PointTangentSeparation
import Langlands.AlgebraicGeometry.Modules.DerivedSections
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Sections of the Poincaré bundle along a nonzero tangent vector at the origin -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.AlgebraicGeometry.Modules.DerivedSections

/-- Let `A` be an abelian scheme over an algebraically closed field `K`, with chosen dual
`D = dualScheme A hA` and Poincaré line bundle `P` on `A ×_K D`. Let `t : Spec K[ε] ⟶ D` be a
nonzero tangent vector at the origin of `D`, and let `X` be a fibre product of the projection
`A ×_K D ⟶ D` and `t`, with projections `q : X ⟶ A ×_K D` and `f : X ⟶ Spec K[ε]`. Then the
`K[ε]`-module of global sections of `q^* P` is not free of rank one.
This definition states a proposition and does not prove it. -/
def AlgClosedFieldPoincareTangentSectionsStatement : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K]
    (A : AbelianScheme (Spec (CommRingCat.of K))) (hA : HasDualScheme A)
    (t : Spec (CommRingCat.of (DualNumber K)) ⟶ (dualScheme A hA).left),
    IsNonzeroTangentVectorAt (dualScheme A hA).hom (dualOrigin A hA).left t →
    ∀ (X : Scheme.{u}) (q : X ⟶ ((baseChange (dualScheme A hA).hom).obj A).X.left)
      (f : X ⟶ Spec (CommRingCat.of (DualNumber K))),
      IsPullback q f ((baseChange (dualScheme A hA).hom).obj A).X.hom t →
      IsEmpty ((relativeGlobalSections f).obj
          ((Scheme.Modules.pullback q).obj (poincareLineBundle A hA).obj) ≅
        ModuleCat.of (DualNumber K) (DualNumber K))

end Langlands.AbelianScheme
