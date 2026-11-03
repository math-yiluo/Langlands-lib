import Langlands.AlgebraicGeometry.Picard.SmoothAutomorphismEtaleAtlasStatement
import Langlands.AlgebraicGeometry.Picard.SmoothAutomorphismQuotientReduction
import Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothRelationQuotientProof

/-! # An etale atlas for the actual Picard class sheaf -/

universe u

namespace Langlands.AlgebraicGeometry.Picard

/-- A locally finite type smooth presentation and smooth relative automorphisms
give the actual etale Picard class sheaf a representable diagonal and a
surjective etale scheme atlas locally of finite type over the base. -/
theorem smoothAutomorphismEtaleAtlas : SmoothAutomorphismEtaleAtlasStatement.{u} :=
  smoothAutomorphismEtaleAtlas_of_smoothRelationQuotient.{u}
    AlgebraicSpace.smoothRelationQuotient.{u}

end Langlands.AlgebraicGeometry.Picard
