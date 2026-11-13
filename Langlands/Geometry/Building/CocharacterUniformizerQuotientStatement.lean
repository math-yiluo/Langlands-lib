import Langlands.Geometry.Building.CocharacterUniformizer
import Langlands.GroupScheme.Rational.RelativeCentralDirections
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.LinearAlgebra.Quotient.Basic

/-! # Integral and common-uniformizer quotients -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.CocharacterUniformizer

/-- Quotienting the common-uniformizer subgroup by the image of another
common-uniformizer subgroup agrees, on every representative, with quotienting
the actual integral cocharacter lattice by postcomposition. -/
def QuotientComparisonStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (A T : CommGroupScheme (Spec (CommRingCat.of F)))
    (_hT : IsSplitTorus T.toGrp) (f : A ⟶ T),
    let N := (CA F A).map (rationalPoints.map (CommGroupScheme.groupHom f))
    let q := QuotientGroup.mk' N
    ∃ e : Multiplicative
        (cocharacterLattice T ⧸ (RealTorusSpace.cocharacterMapInt f).range) ≃*
          (CA F T).map q,
      ∀ c : cocharacterLattice T,
        (e (Multiplicative.ofAdd ((RealTorusSpace.cocharacterMapInt f).range.mkQ c)) :
          rationalPoints T.toGrp ⧸ N) =
            q (latticeSection F T (Multiplicative.ofAdd c))

end Langlands.GroupScheme.CocharacterUniformizer
