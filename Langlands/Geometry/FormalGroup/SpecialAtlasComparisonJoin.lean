import Langlands.Geometry.FormalGroup.AtlasOrderComparisonBaseChangeJoin
import Langlands.Geometry.FormalGroup.SpecialAtlasClassReduction

/-! # Joining specified special-atlas comparisons through quotient reduction -/

noncomputable section

universe u v s

namespace Langlands.FormalGroup.LocalDivision.SpecialAtlas

open CategoryTheory ValuativeRel CentralDivision ModuleLaw

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] {ι : L →ₐ[K] D}
variable {R S : Type v} [CommRing R] [CommRing S]

attribute [local instance] coefficientAlgebra coefficientScalarTower

section AlgebraTransport

variable {α : Algebra 𝒪[K] R}
variable {X Y Z : (letI := α; SpecialAtlas K D ι R)}

/-- Retype the supplied middle-cover equality with both actual comparisons. -/
theorem reAlgebraComparisonJoinCover (c : (letI := α; Comparison X Y))
    (d : (letI := α; Comparison Y Z)) (h : c.right.opens = d.left.opens)
    (β : Algebra 𝒪[K] R) (e : α = β) :
    (letI := β; (reAlgebraComparison c β e).right.opens =
      (reAlgebraComparison d β e).left.opens) := by
  cases e
  exact h

/-- Equal scalar structures transport the same actual joined formal maps. -/
theorem reAlgebraComparison_join (c : (letI := α; Comparison X Y))
    (d : (letI := α; Comparison Y Z)) (h : c.right.opens = d.left.opens)
    (β : Algebra 𝒪[K] R) (e : α = β) :
    (letI := α; reAlgebraComparison (c.join d h) β e) =
      (letI := β; (reAlgebraComparison c β e).join (reAlgebraComparison d β e)
        (reAlgebraComparisonJoinCover c d h β e)) := by
  cases e
  rfl

end AlgebraTransport

variable [Algebra 𝒪[K] R] [Algebra 𝒪[K] S]
variable {X Y Z : SpecialAtlas K D ι R}

/-- Extend and retype the specified middle-cover equality to the supplied scalars. -/
theorem baseChangeAlongComparisonJoinCover (c : Comparison X Y) (d : Comparison Y Z)
    (h : c.right.opens = d.left.opens) (f : R →ₐ[𝒪[K]] S) :
    (baseChangeAlongComparison c f).right.opens =
      (baseChangeAlongComparison d f).left.opens :=
  reAlgebraComparisonJoinCover (baseChangeComparison c (BasicAtlas.coefficientTest f))
    (baseChangeComparison d (BasicAtlas.coefficientTest f))
    (BasicAtlas.baseOpens_eq (BasicAtlas.coefficientTest f) h) _
    (BasicAtlas.coefficientAlgebraAlong_eq f)

/-- Supplied-target extension preserves the specified whole formal join. -/
theorem baseChangeAlongComparison_join (c : Comparison X Y) (d : Comparison Y Z)
    (h : c.right.opens = d.left.opens) (f : R →ₐ[𝒪[K]] S) :
    baseChangeAlongComparison (c.join d h) f =
      (baseChangeAlongComparison c f).join (baseChangeAlongComparison d f)
        (baseChangeAlongComparisonJoinCover c d h f) := by
  let T : CommAlgCat.{v} R := BasicAtlas.coefficientTest f
  unfold baseChangeAlongComparison baseChangeComparison
  rw [BasicAtlas.OrderAction.Comparison.baseChange_join]
  exact reAlgebraComparison_join
    (baseChangeComparison c T) (baseChangeComparison d T)
    (BasicAtlas.baseOpens_eq T h) _ (BasicAtlas.coefficientAlgebraAlong_eq f)

variable {r : R} {A : Nilp.{v, u} R r}

/-- The actual quotient map preserves the supplied middle-cover equality. -/
theorem reductionComparisonJoinCover {X Y Z : SpecialAtlas K D ι A.obj}
    (c : Comparison X Y) (d : Comparison Y Z) (h : c.right.opens = d.left.opens) :
    (reductionComparison c).right.opens = (reductionComparison d).left.opens :=
  baseChangeAlongComparisonJoinCover c d h (Nilp.quotientO 𝒪[K] A)

/-- Quotient reduction preserves exactly the joined comparison and its source maps. -/
theorem reductionComparison_join {X Y Z : SpecialAtlas K D ι A.obj}
    (c : Comparison X Y) (d : Comparison Y Z) (h : c.right.opens = d.left.opens) :
    reductionComparison (c.join d h) =
      (reductionComparison c).join (reductionComparison d)
        (reductionComparisonJoinCover c d h) :=
  baseChangeAlongComparison_join c d h (Nilp.quotientO 𝒪[K] A)

end Langlands.FormalGroup.LocalDivision.SpecialAtlas
