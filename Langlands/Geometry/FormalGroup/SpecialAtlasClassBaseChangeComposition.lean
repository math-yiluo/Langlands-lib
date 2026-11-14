import Langlands.Geometry.FormalGroup.SpecialAtlasClassBaseChange
import Langlands.Geometry.FormalGroup.AtlasOrderBaseChangeComposition

/-! # Composition of coefficient maps on actual special-atlas classes -/

noncomputable section

universe u v s

namespace Langlands.FormalGroup.LocalDivision.SpecialAtlas

open CategoryTheory ValuativeRel CentralDivision ModuleLaw

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] {ι : L →ₐ[K] D}
variable {R : Type v} [CommRing R] [Algebra 𝒪[K] R]

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- Successive and direct coefficient extensions compare by actual full-order formal maps. -/
def baseCompComparison (X : SpecialAtlas K D ι R)
    (S : CommAlgCat.{v} R) (T : CommAlgCat.{v} S) :
    Comparison ((X.baseChange S).baseChange T)
      (X.baseChange (BasicAtlas.restrictTest S T)) where
  left := BasicAtlas.CoverRefinement.refl _
  right := (BasicAtlas.CoverRefinement.refl _).retarget _ (X.atlas.baseCompOpens_eq S T)
  sameCover := rfl
  coordinateIso := (X.order.baseCompIso S T).restrict (BasicAtlas.CoverRefinement.refl _)

/-- The constructed formal comparison identifies the two actual special-atlas classes. -/
theorem classOf_baseChange_comp (X : SpecialAtlas K D ι R)
    (S : CommAlgCat.{v} R) (T : CommAlgCat.{v} S) :
    classOf ((X.baseChange S).baseChange T) =
      classOf (X.baseChange (BasicAtlas.restrictTest S T)) :=
  classOf_eq_of_comparison (X.baseCompComparison S T)

namespace IsoClass

/-- The quotient coefficient maps compose through the actual structural composite. -/
theorem baseChange_comp (q : IsoClass (K := K) (D := D) (ι := ι) (R := R))
    (S : CommAlgCat.{v} R) (T : CommAlgCat.{v} S) :
    (q.baseChange S).baseChange T = q.baseChange (BasicAtlas.restrictTest S T) := by
  refine Quotient.inductionOn q ?_
  intro X
  exact classOf_baseChange_comp X S T

end IsoClass

namespace HeightSquaredAtlas

variable {π : 𝒪[K]}

/-- Both actual extended representatives retain their own height certificates. -/
theorem classOf_baseChange_comp
    (X : HeightSquaredAtlas (K := K) (D := D) (ι := ι) (R := R) π)
    (S : CommAlgCat.{v} R) (T : CommAlgCat.{v} S) :
    classOf ((X.baseChange S).baseChange T) =
      classOf (X.baseChange (BasicAtlas.restrictTest S T)) :=
  classOf_eq_of_comparison (X.val.baseCompComparison S T)

namespace IsoClass

/-- Coefficient composition also holds inside the actual height-certified quotient. -/
theorem baseChange_comp (q : IsoClass (K := K) (D := D) (ι := ι) (R := R) π)
    (S : CommAlgCat.{v} R) (T : CommAlgCat.{v} S) :
    (q.baseChange S).baseChange T = q.baseChange (BasicAtlas.restrictTest S T) := by
  refine Quotient.inductionOn q ?_
  intro X
  exact classOf_baseChange_comp X S T

end IsoClass

end HeightSquaredAtlas

end Langlands.FormalGroup.LocalDivision.SpecialAtlas
