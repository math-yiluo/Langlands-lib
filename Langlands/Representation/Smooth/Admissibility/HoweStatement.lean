import Langlands.Representation.Category.Basic
import Langlands.AlgebraicGeometry.PointTopology.RationalPoints
import Langlands.GroupScheme.Reductive.Basic
import Mathlib.NumberTheory.LocalField.Basic

/-!
# Howe's finite-length implication on actual reductive rational points

The finitely generated admissible implication of Renard VI.6.3, for the
canonical identity-test rational-point topology. This is a statement only.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme

namespace Langlands.SmoothRep

universe u uV

/-- A finitely generated admissible smooth complex representation of the
rational points of a connected reductive group over a nonarchimedean local
field has finite length (Renard VI.6.3). Finite generation and finite length
refer to the actual group-algebra module. -/
def RationalPointsFinitelyGeneratedAdmissibleFiniteLengthStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (RationalPoint F G.X) := rationalPointTopology F G.X
    ∀ A : SmoothRep.{0, u, uV} ℂ (RationalPoint F G.X),
      Module.Finite (MonoidAlgebra ℂ (RationalPoint F G.X))
        A.representation.asModule →
          A.IsAdmissible → A.HasFiniteLength

end Langlands.SmoothRep
