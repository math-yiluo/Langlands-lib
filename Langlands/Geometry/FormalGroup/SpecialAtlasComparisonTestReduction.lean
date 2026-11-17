import Langlands.Geometry.FormalGroup.SpecialAtlasComparisonTestSources
import Langlands.Geometry.FormalGroup.SpecialAtlasClassReduction

/-! # Actual test-comparison naturality for reduction and Nilp base change -/

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

/-- Actual refined test comparisons commute with the canonical Nilp quotient-square maps. -/
theorem testIso_reductionBaseChange (c : Comparison X Y) (f : A ⟶ B)
    (C : CommAlgCat.{w} ((Nilp.reductionFunctor R r).obj B).obj)
    (b : (reductionComparison (baseChangeAlongComparison c (Nilp.scalarMap 𝒪[K] f))).right.opens)
    (hb : IsUnit (algebraMap ((Nilp.reductionFunctor R r).obj B).obj C b.val))
    (b' : (baseChangeAlongComparison (reductionComparison c)
      (Nilp.reducedScalarMap 𝒪[K] f)).right.opens)
    (hb' : IsUnit (algebraMap ((Nilp.reductionFunctor R r).obj B).obj C b'.val))
    (x : (X.reduction.baseChangeAlong (Nilp.reducedScalarMap 𝒪[K] f)).atlas.opens)
    (y : (Y.reduction.baseChangeAlong (Nilp.reducedScalarMap 𝒪[K] f)).atlas.opens)
    (hx : IsUnit (algebraMap ((Nilp.reductionFunctor R r).obj B).obj C x.val))
    (hy : IsUnit (algebraMap ((Nilp.reductionFunctor R r).obj B).obj C y.val)) :
    ((reductionComparison (baseChangeAlongComparison c (Nilp.scalarMap 𝒪[K] f))).testIso C b hb
      (BasicAtlas.sourceChart (X.atlas.reductionBaseChangeOpens_eq f) x)
      (BasicAtlas.sourceChart (Y.atlas.reductionBaseChangeOpens_eq f) y) hx hy).trans
        ((Y.reductionBaseChangeIso f).onChart C y hy) =
      ((X.reductionBaseChangeIso f).onChart C x hx).trans
        ((baseChangeAlongComparison (reductionComparison c)
          (Nilp.reducedScalarMap 𝒪[K] f)).testIso C b' hb' x y hx hy) :=
  testIso_baseAlongSquare_onCharts c (Nilp.scalarMap 𝒪[K] f) (Nilp.quotientO 𝒪[K] B)
    (Nilp.quotientO 𝒪[K] A) (Nilp.reducedScalarMap 𝒪[K] f) (Nilp.quotientO_natural 𝒪[K] f)
    C b hb b' hb' x y hx hy

/-- Select an actual original reduced finer chart from the given new reduced comparison chart. -/
def reductionBaseChangeOriginalChart (c : Comparison X Y) (f : A ⟶ B)
    (b : (reductionComparison (baseChangeAlongComparison c (Nilp.scalarMap 𝒪[K] f))).right.opens) :
    (reductionComparison c).right.opens :=
  baseChangeAlongComparisonImageChart c (Nilp.quotientO 𝒪[K] A)
    (baseAlongCompOriginalChart c (Nilp.scalarMap 𝒪[K] f) (Nilp.quotientO 𝒪[K] B) b)

/-- The selected actual old reduced chart is invertible on the restricted new quotient test. -/
theorem reductionBaseChangeOriginalChart_unit (c : Comparison X Y) (f : A ⟶ B)
    (C : CommAlgCat.{w} ((Nilp.reductionFunctor R r).obj B).obj)
    (b : (reductionComparison (baseChangeAlongComparison c (Nilp.scalarMap 𝒪[K] f))).right.opens)
    (hb : IsUnit (algebraMap ((Nilp.reductionFunctor R r).obj B).obj C b.val)) :
    IsUnit (algebraMap ((Nilp.reductionFunctor R r).obj A).obj
      (restrictCoefficientAlgebra (Nilp.reducedScalarMap 𝒪[K] f) C)
        (reductionBaseChangeOriginalChart c f b).val) := by
  let a := baseAlongCompOriginalChart c (Nilp.scalarMap 𝒪[K] f) (Nilp.quotientO 𝒪[K] B) b
  have ha := baseAlongCompOriginalChart_unit c (Nilp.scalarMap 𝒪[K] f)
    (Nilp.quotientO 𝒪[K] B) C b hb
  have hqa : IsUnit (algebraMap ((Nilp.reductionFunctor R r).obj B).obj C
      (((Nilp.reducedScalarMap 𝒪[K] f).comp (Nilp.quotientO 𝒪[K] A)) a.val)) := by
    have hna : IsUnit (algebraMap ((Nilp.reductionFunctor R r).obj B).obj C
      (((Nilp.quotientO 𝒪[K] B).comp (Nilp.scalarMap 𝒪[K] f)) a.val)) := ha
    simpa only [Nilp.quotientO_natural 𝒪[K] f] using hna
  exact baseChangeAlongComparisonImageChart_unit c (Nilp.quotientO 𝒪[K] A)
    (restrictCoefficientAlgebra (Nilp.reducedScalarMap 𝒪[K] f) C) a hqa

/-- Image the same actual original reduced finer chart into the extended old reduced comparison. -/
def reductionBaseChangeOldImageChart (c : Comparison X Y) (f : A ⟶ B)
    (b : (reductionComparison (baseChangeAlongComparison c (Nilp.scalarMap 𝒪[K] f))).right.opens) :=
  baseChangeAlongComparisonImageChart (reductionComparison c) (Nilp.reducedScalarMap 𝒪[K] f)
    (reductionBaseChangeOriginalChart c f b)

/-- Its actual generator is invertible on the supplied new quotient test. -/
theorem reductionBaseChangeOldImageChart_unit (c : Comparison X Y) (f : A ⟶ B)
    (C : CommAlgCat.{w} ((Nilp.reductionFunctor R r).obj B).obj)
    (b : (reductionComparison (baseChangeAlongComparison c (Nilp.scalarMap 𝒪[K] f))).right.opens)
    (hb : IsUnit (algebraMap ((Nilp.reductionFunctor R r).obj B).obj C b.val)) :
    IsUnit (algebraMap ((Nilp.reductionFunctor R r).obj B).obj C
      (reductionBaseChangeOldImageChart c f b).val) :=
  baseChangeAlongComparisonImageChart_unit (reductionComparison c)
    (Nilp.reducedScalarMap 𝒪[K] f) C (reductionBaseChangeOriginalChart c f b)
    (reductionBaseChangeOriginalChart_unit c f C b hb)

/-- The actual Nilp quotient-square test comparison with both old finer charts constructed. -/
def reductionBaseChangeTestSquare (c : Comparison X Y) (f : A ⟶ B)
    (C : CommAlgCat.{w} ((Nilp.reductionFunctor R r).obj B).obj)
    (b : (reductionComparison (baseChangeAlongComparison c (Nilp.scalarMap 𝒪[K] f))).right.opens)
    (hb : IsUnit (algebraMap ((Nilp.reductionFunctor R r).obj B).obj C b.val))
    (x : (X.reduction.baseChangeAlong (Nilp.reducedScalarMap 𝒪[K] f)).atlas.opens)
    (y : (Y.reduction.baseChangeAlong (Nilp.reducedScalarMap 𝒪[K] f)).atlas.opens)
    (hx : IsUnit (algebraMap ((Nilp.reductionFunctor R r).obj B).obj C x.val))
    (hy : IsUnit (algebraMap ((Nilp.reductionFunctor R r).obj B).obj C y.val)) :=
  ModuleLaw.OrderAction.Iso.rationalSquare (F := K)
    ((reductionComparison (baseChangeAlongComparison c (Nilp.scalarMap 𝒪[K] f))).testIso C b hb
      (BasicAtlas.sourceChart (X.atlas.reductionBaseChangeOpens_eq f) x)
      (BasicAtlas.sourceChart (Y.atlas.reductionBaseChangeOpens_eq f) y) hx hy)
    ((Y.reductionBaseChangeIso f).onChart C y hy)
    ((X.reductionBaseChangeIso f).onChart C x hx)
    ((baseChangeAlongComparison (reductionComparison c) (Nilp.reducedScalarMap 𝒪[K] f)).testIso C
      (reductionBaseChangeOldImageChart c f b) (reductionBaseChangeOldImageChart_unit c f C b hb)
      x y hx hy)
    (testIso_reductionBaseChange c f C b hb (reductionBaseChangeOldImageChart c f b)
      (reductionBaseChangeOldImageChart_unit c f C b hb) x y hx hy)

end Langlands.FormalGroup.LocalDivision.SpecialAtlas
