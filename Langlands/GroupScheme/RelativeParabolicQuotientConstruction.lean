import Langlands.GroupScheme.RelativeParabolicQuotientReduction
import Langlands.AlgebraicGeometry.ProperOfFibres.ProperAmbientCriterionProof

/-! # Relative parabolic quotients from two structural inputs -/

noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeParabolicQuotient

variable {R : Type u} [CommRing R]
    {G P : GroupScheme (Spec (CommRingCat.of R))} {i : P ⟶ G}

/-- Construct the actual proper quotient using the published properness proof.
Only the parabolic-dynamic and proper-ambient statements remain as inputs. -/
def properQuotientOfDynamicAndAmbient
    (hPD : ParabolicDynamicStatement.{u})
    (hambient : SelfNormalizingProperAmbientStatement.{u})
    (hG : IsReductive G) (hPsmooth : Smooth P.X.hom) (hi : IsClosedSubgroup i)
    (hP : ∀ (k : Type u) [Field k] [Algebra R k],
      IsParabolicSubgroup ((GroupScheme.baseChange (Spec.algebraMap R k)).map i)) :
    ProperHomogeneousQuotient i :=
  RelativeParabolicQuotientReduction.properQuotientOfDynamicAndAmbient
    hPD hambient properAmbientCriterion_holds hG hPsmooth hi hP

/-- Extract exactly the published existence conclusion from the two remaining
structural statements; generic properness is supplied by its published proof. -/
theorem existenceStatement_of_dynamic_and_ambient
    (hPD : ParabolicDynamicStatement.{u})
    (hambient : SelfNormalizingProperAmbientStatement.{u}) :
    ExistenceStatement.{u} :=
  RelativeParabolicQuotientReduction.existenceStatement_of_dynamic_and_ambient
    hPD hambient properAmbientCriterion_holds

end Langlands.GroupScheme.RelativeParabolicQuotient
