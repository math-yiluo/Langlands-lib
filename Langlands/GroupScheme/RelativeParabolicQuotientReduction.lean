import Langlands.GroupScheme.RelativeParabolicQuotientAssembly
import Langlands.GroupScheme.RelativeSelfNormalizerProof
import Langlands.GroupScheme.Rational.ParabolicNormalizerDescent
import Langlands.GroupScheme.Absolute.BorelConjugacyProof
import Langlands.GroupScheme.Absolute.BorelNormalizerProof

/-! # Relative parabolic quotients with the normalizer inputs discharged -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeParabolicQuotientReduction

/-- The published rational descent reduction discharges the field self-normalizer
input once the parabolic-dynamic statement is supplied. -/
theorem fieldSelfNormalizer_of_parabolicDynamic
    (hPD : ParabolicDynamicStatement.{u}) : ParabolicSelfNormalizerStatement.{u} :=
  parabolicSelfNormalizerStatement_of_rational_descent
    borelConjugacy borelNormalizer hPD dynamicConnected

variable {R : Type u} [CommRing R]
    {G P : GroupScheme (Spec (CommRingCat.of R))} {i : P ⟶ G}

/-- All-test self-normalization of the original relative parabolic subgroup,
conditional only on the parabolic-dynamic characterization. -/
theorem normalizer_eq_of_parabolicDynamic
    (hPD : ParabolicDynamicStatement.{u})
    (hG : IsReductive G) (hPsmooth : Smooth P.X.hom) (hi : IsClosedSubgroup i)
    (hP : ∀ (k : Type u) [Field k] [Algebra R k],
      IsParabolicSubgroup ((GroupScheme.baseChange (Spec.algebraMap R k)).map i)) :
    (SubgroupFunctor.range i).normalizer = SubgroupFunctor.range i :=
  RelativeParabolicNormalizerReduction.normalizer_eq_of_statements
    relativeSelfNormalizer (fieldSelfNormalizer_of_parabolicDynamic hPD)
    hPD hG hPsmooth hi hP

/-- Construct the actual proper quotient with no independent relative or field
self-normalizer premise. The three remaining structural inputs are explicit. -/
def properQuotientOfDynamicAndAmbient
    (hPD : ParabolicDynamicStatement.{u})
    (hambient : SelfNormalizingProperAmbientStatement.{u})
    (hproper : RelativeParabolicQuotient.ProperAmbientCriterion.{u})
    (hG : IsReductive G) (hPsmooth : Smooth P.X.hom) (hi : IsClosedSubgroup i)
    (hP : ∀ (k : Type u) [Field k] [Algebra R k],
      IsParabolicSubgroup ((GroupScheme.baseChange (Spec.algebraMap R k)).map i)) :
    RelativeParabolicQuotient.ProperHomogeneousQuotient i :=
  RelativeParabolicQuotient.properQuotientOfStatements
    relativeSelfNormalizer (fieldSelfNormalizer_of_parabolicDynamic hPD)
    hPD hambient hproper hG hPsmooth hi hP

/-- The exact published existence conclusion, conditional on precisely the
parabolic-dynamic, proper-ambient and generic properness statements. -/
theorem existenceStatement_of_dynamic_and_ambient
    (hPD : ParabolicDynamicStatement.{u})
    (hambient : SelfNormalizingProperAmbientStatement.{u})
    (hproper : RelativeParabolicQuotient.ProperAmbientCriterion.{u}) :
    RelativeParabolicQuotient.ExistenceStatement.{u} :=
  RelativeParabolicQuotient.existenceStatement_of_statements
    relativeSelfNormalizer (fieldSelfNormalizer_of_parabolicDynamic hPD)
    hPD hambient hproper

end Langlands.GroupScheme.RelativeParabolicQuotientReduction
