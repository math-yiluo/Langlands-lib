import Langlands.Geometry.Building.CocharacterUniformizerConeQuotientStatement
import Mathlib.GroupTheory.Finiteness

/-! # Finite generation of the actual nonnegative uniformizer quotient -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.CocharacterUniformizer

/-- The nonnegative common-uniformizer monoid modulo the actual split
component is finitely generated. -/
def ConeQuotientFiniteGenerationStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of F)))
    (i : T.toGrp ⟶ G) (_hi : IsMaximalSplitTorus i),
    haveI := hG.isAffineHom
    ∀ (ν : cocharacterLattice T), IsGenericCocharacter i ν →
      ∀ (A : CommGroupScheme (Spec (CommRingCat.of F))) (a : A.toGrp ⟶ G),
        IsSplitComponent a → ∀ (f : A ⟶ T),
          CommGroupScheme.groupHom f ≫ i = a →
            (CAplusQuotient F T (simpleRelativeRoots i ν) A f).FG

end Langlands.GroupScheme.CocharacterUniformizer
