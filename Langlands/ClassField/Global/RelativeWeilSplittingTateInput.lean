import Langlands.ClassField.Global.IdeleClassFundamentalTateInput
import Langlands.ClassField.Global.RelativeWeilGroup
import Langlands.GroupTheory.CocycleSplittingClass

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits NumberField
open scoped NumberField

namespace Langlands.ClassField.Global.RelativeWeilGroup

set_option backward.isDefEq.respectTransparency false

attribute [local instance] relativeIdeleClassAction

variable (c : FundamentalClass.ClassFamily.{u}) (F E : Type u)
  [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra F E] [IsGalois F E]

/-- The actual splitting representation of the chosen cocycle defining
the relative Weil group. -/
def splittingRepresentation :
    Rep.{u} NormalizedTwoCocycle.CoefficientScalars.{u} (E ≃ₐ[F] E) := by
  letI := Fintype.ofFinite (E ≃ₐ[F] E)
  exact NormalizedTwoCocycle.SplittingModule.splitting
    (ClassExtension.representative (c F E))

/-- A generating, restriction-compatible family makes the chosen relative
Weil splitting representation acyclic in every Tate degree. -/
lemma splittingRepresentation_tate_isZero
    (hgen : FundamentalClass.Generates c) (hres : FundamentalClass.Restriction c)
    (n : ℤ) :
    letI := Fintype.ofFinite (E ≃ₐ[F] E)
    IsZero (tateCohomology (splittingRepresentation c F E) n) := by
  let := Fintype.ofFinite (E ≃ₐ[F] E)
  apply NormalizedTwoCocycle.SplittingModule.splitting_tate_isZero
    (ClassExtension.representative (c F E))
  intro m
  rw [show NormalizedTwoCocycle.cohomologyClass (ClassExtension.representative (c F E)) =
    c F E from ClassExtension.cohomologyClass_representative (c F E)]
  exact fundamentalClass_tateCup_bijective F E c hgen hres m

end Langlands.ClassField.Global.RelativeWeilGroup
