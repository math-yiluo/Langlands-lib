import Langlands.Geometry.Analytic.SpaceAnalytificationExistenceStatement
import Langlands.Geometry.Analytic.AffineAnalytificationScalarExtension
import Langlands.Geometry.Analytic.LocalizedGroundFieldExtension
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceBaseChange

/-! # Analytification and extension of the ground field -/

noncomputable section

universe u

namespace Langlands.Analytic.SpaceAnalytification

open CategoryTheory SaturatedAtlasPresentation
open AffinoidAtlasPresentation.GroundFieldExtension (localizedFunctor localizedProjection)
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.AlgebraicSpace
open scoped TensorProduct

/-- Over a complete nontrivially valued nonarchimedean extension `L/K`, the ground field
extension of an analytification of a separated algebraic space analytifies the algebraic
base change. The affine comparisons commute with the analytified test maps and with
restriction of seminorms. -/
def SpaceAnalytificationGroundFieldStatement : Prop :=
  ∀ (K L : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L] [NormedAlgebra K L]
    (X : AlgebraicSpace (Spec (CommRingCat.of K))),
    IsSeparated X → LocallyOfFiniteTypeOverBase X →
    ∀ (Y : LocalizedCategory.{u, u, u} (K := K)) (p : PointFamily K X Y),
      IsAnalytification K X Y p →
      let XL := baseChange (Spec.algebraMap K L) X
      let F := localizedFunctor.{u, u, u, u} K L
      ∃ q : PointFamily L XL (F.obj Y),
        IsAnalytification L XL (F.obj Y) q ∧
        ∀ (A : Type u) [CommRing A] [Algebra K A] (P : FinitePolynomialPresentation K A),
          let Q := AffineAnalytification.baseChangePresentation K L P
          let U := AffineAnalytification.localized K P
          ∃ c : F.obj U ≅ AffineAnalytification.localized L Q,
            (∀ (z : AffineAnalytification.Space L Q),
              ((localizedProjection K L).app U
                (ULift.up (localizedSpaceFunctor.map c.inv z))).down =
                AffineAnalytification.baseChangeMap K L P z) ∧
            ∀ x : RingPoints K X A,
              let xL := (baseChangeRingPointsEquiv K L (L ⊗[K] A) X).symm
                (RingPoints.changeRing Algebra.TensorProduct.includeRight x)
              c.hom ≫ q (L ⊗[K] A) Q xL = F.map (p A P x)

end Langlands.Analytic.SpaceAnalytification
