import Langlands.Geometry.Building.CocharacterUniformizerCone
import Langlands.GroupScheme.Rational.SimpleRootSplitCentralImageStatement

/-! # The nonnegative cocharacter and actual split-central quotients -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.CocharacterUniformizer

/-- The nonnegative integral quotient models the actual common-uniformizer
monoid modulo the split component, with its prescribed representative map. -/
def ConeQuotientComparisonStatement : Prop :=
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
            let R := simpleRelativeRoots i ν
            let P := RealTorusSpace.rootAnnihilatorInt T R
            let N := (CA F A).map (rationalPoints.map (CommGroupScheme.groupHom f))
            let q := QuotientGroup.mk' N
            ∃ e : Multiplicative (CocharacterCone.quotient T R) ≃*
                CAplusQuotient F T R A f,
              ∀ (c : cocharacterLattice T) (hc : c ∈ CocharacterCone.nonnegative T R),
                (e (Multiplicative.ofAdd
                  ⟨P.mkQ c, ⟨c, hc, rfl⟩⟩) : rationalPoints T.toGrp ⧸ N) =
                    q (latticeSection F T (Multiplicative.ofAdd c))

end Langlands.GroupScheme.CocharacterUniformizer
