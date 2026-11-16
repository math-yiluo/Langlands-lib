import Langlands.Geometry.FormalGroup.SpecialAtlasReduction
import Langlands.Geometry.FormalGroup.SpecialAtlasClassFunctor
import Langlands.Geometry.FormalGroup.AtlasOrderReductionBaseChange

/-! # Quotient reduction on actual special-atlas comparison classes -/

noncomputable section

universe u v w s

namespace Langlands.FormalGroup.LocalDivision.SpecialAtlas

open CategoryTheory ValuativeRel CentralDivision ModuleLaw

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] {ι : L →ₐ[K] D}
variable {R : Type v} [CommRing R] [Algebra 𝒪[K] R] {r : R}
variable {A B : Nilp.{v, w} R r}

attribute [local instance] coefficientAlgebra coefficientScalarTower

variable {X Y : SpecialAtlas K D ι A.obj}

/-- Reduce the specified actual formal comparison after its two principal refinements. -/
def reductionComparison (g : Comparison X Y) : Comparison X.reduction Y.reduction :=
  baseChangeAlongComparison g (Nilp.quotientO 𝒪[K] A)

/-- The reduced specified comparison realizes the square on complete compatible families. -/
theorem reductionComparison_onPoints (g : Comparison X Y)
    (C : CommAlgCat.{w} ((Nilp.reductionFunctor R r).obj A).obj)
    (x : X.Point (restrictCoefficientAlgebra (Nilp.quotientO 𝒪[K] A) C)) :
    (reductionComparison g).onPoints C (X.reductionPointEquiv C x) =
      Y.reductionPointEquiv C
        (g.onPoints (restrictCoefficientAlgebra (Nilp.quotientO 𝒪[K] A) C) x) :=
  baseChangeAlongComparison_onPoints g (Nilp.quotientO 𝒪[K] A) C x

/-- The inverse family comparisons realize the reverse square for the same formal comparison. -/
theorem reductionComparison_fromPoints (g : Comparison X Y)
    (C : CommAlgCat.{w} ((Nilp.reductionFunctor R r).obj A).obj)
    (y : X.reduction.Point C) :
    g.onPoints (restrictCoefficientAlgebra (Nilp.quotientO 𝒪[K] A) C)
        ((X.reductionPointEquiv C).symm y) =
      (Y.reductionPointEquiv C).symm ((reductionComparison g).onPoints C y) :=
  baseChangeAlongComparison_fromPoints g (Nilp.quotientO 𝒪[K] A) C y

/-- Reduction preserves existence of actual refined full-order formal comparison. -/
theorem equivalent_reduction (h : Equivalent X Y) : Equivalent X.reduction Y.reduction :=
  equivalent_baseChangeAlong h (Nilp.quotientO 𝒪[K] A)

/-- Changing the Nilp base and then reducing compares by actual full-order formal maps. -/
def reductionBaseChangeIso (X : SpecialAtlas K D ι A.obj) (f : A ⟶ B) :
    ((X.baseChangeAlong (Nilp.scalarMap 𝒪[K] f)).reduction (A := B)).Iso
      (X.reduction.baseChangeAlong (Nilp.reducedScalarMap 𝒪[K] f))
      (X.atlas.reductionBaseChangeOpens_eq f) :=
  X.order.reductionBaseChangeIso f

/-- Both actual maps and inverse equations give an actual refined formal comparison. -/
def reductionBaseChangeComparison (X : SpecialAtlas K D ι A.obj) (f : A ⟶ B) :
    Comparison ((X.baseChangeAlong (Nilp.scalarMap 𝒪[K] f)).reduction (A := B))
      (X.reduction.baseChangeAlong (Nilp.reducedScalarMap 𝒪[K] f)) where
  left := BasicAtlas.CoverRefinement.refl _
  right := (BasicAtlas.CoverRefinement.refl _).retarget _
    (X.atlas.reductionBaseChangeOpens_eq f)
  sameCover := rfl
  coordinateIso := (X.reductionBaseChangeIso f).restrict (BasicAtlas.CoverRefinement.refl _)

/-- The actual quotient-square comparison identifies the two special-atlas classes. -/
theorem classOf_reduction_baseChangeAlong (X : SpecialAtlas K D ι A.obj) (f : A ⟶ B) :
    classOf ((X.baseChangeAlong (Nilp.scalarMap 𝒪[K] f)).reduction (A := B)) =
      classOf (X.reduction.baseChangeAlong (Nilp.reducedScalarMap 𝒪[K] f)) :=
  classOf_eq_of_comparison (X.reductionBaseChangeComparison f)

namespace IsoClass

/-- Descend actual quotient extension through the actual formal comparison relation. -/
def reduction (q : IsoClass (K := K) (D := D) (ι := ι) (R := A.obj)) :
    IsoClass (K := K) (D := D) (ι := ι) (R := ((Nilp.reductionFunctor R r).obj A).obj) :=
  q.baseChangeAlong (Nilp.quotientO 𝒪[K] A)

@[simp]
theorem reduction_classOf (X : SpecialAtlas K D ι A.obj) :
    (classOf X).reduction = classOf X.reduction := rfl

/-- Quotient reduction is natural in actual varying-Nilp coefficient maps. -/
theorem reduction_baseChangeAlong
    (q : IsoClass (K := K) (D := D) (ι := ι) (R := A.obj)) (f : A ⟶ B) :
    (q.baseChangeAlong (Nilp.scalarMap 𝒪[K] f)).reduction (A := B) =
      q.reduction.baseChangeAlong (Nilp.reducedScalarMap 𝒪[K] f) := by
  refine Quotient.inductionOn q ?_
  intro X
  exact classOf_reduction_baseChangeAlong X f

end IsoClass

namespace HeightSquaredAtlas

variable {π : 𝒪[K]}

/-- Reduce the actual atlas together with its own height and base-nilpotence certificates. -/
def reduction (X : HeightSquaredAtlas (K := K) (D := D) (ι := ι) (R := A.obj) π) :
    HeightSquaredAtlas (K := K) (D := D) (ι := ι)
      (R := ((Nilp.reductionFunctor R r).obj A).obj) π :=
  X.baseChangeAlong (Nilp.quotientO 𝒪[K] A)

@[simp]
theorem val_reduction (X : HeightSquaredAtlas (K := K) (D := D) (ι := ι) (R := A.obj) π) :
    X.reduction.val = X.val.reduction := rfl

/-- Both reduced representatives retain their own certificates and the same formal comparison. -/
theorem equivalent_reduction
    {X Y : HeightSquaredAtlas (K := K) (D := D) (ι := ι) (R := A.obj) π}
    (h : Equivalent X Y) : Equivalent X.reduction Y.reduction :=
  SpecialAtlas.equivalent_reduction h

/-- The actual quotient-square comparison also identifies height-certified classes. -/
theorem classOf_reduction_baseChangeAlong
    (X : HeightSquaredAtlas (K := K) (D := D) (ι := ι) (R := A.obj) π) (f : A ⟶ B) :
    classOf ((X.baseChangeAlong (Nilp.scalarMap 𝒪[K] f)).reduction (A := B)) =
      classOf (X.reduction.baseChangeAlong (Nilp.reducedScalarMap 𝒪[K] f)) :=
  classOf_eq_of_comparison (X.val.reductionBaseChangeComparison f)

namespace IsoClass

/-- Descend quotient extension inside the subtype already carrying actual height d². -/
def reduction (q : IsoClass (K := K) (D := D) (ι := ι) (R := A.obj) π) :
    IsoClass (K := K) (D := D) (ι := ι)
      (R := ((Nilp.reductionFunctor R r).obj A).obj) π :=
  q.baseChangeAlong (Nilp.quotientO 𝒪[K] A)

@[simp]
theorem reduction_classOf
    (X : HeightSquaredAtlas (K := K) (D := D) (ι := ι) (R := A.obj) π) :
    (classOf X).reduction = classOf X.reduction := rfl

/-- Forgetting the height certificates commutes with actual quotient reduction. -/
@[simp]
theorem forgetHeight_reduction
    (q : IsoClass (K := K) (D := D) (ι := ι) (R := A.obj) π) :
    q.reduction.forgetHeight = q.forgetHeight.reduction :=
  q.forgetHeight_baseChangeAlong (Nilp.quotientO 𝒪[K] A)

/-- Quotient reduction is natural within the actual height-certified comparison quotient. -/
theorem reduction_baseChangeAlong
    (q : IsoClass (K := K) (D := D) (ι := ι) (R := A.obj) π) (f : A ⟶ B) :
    (q.baseChangeAlong (Nilp.scalarMap 𝒪[K] f)).reduction (A := B) =
      q.reduction.baseChangeAlong (Nilp.reducedScalarMap 𝒪[K] f) := by
  refine Quotient.inductionOn q ?_
  intro X
  exact classOf_reduction_baseChangeAlong X f

end IsoClass
end HeightSquaredAtlas

end Langlands.FormalGroup.LocalDivision.SpecialAtlas
