import Langlands.Representation.Aubert.General.InductionCoproducts
import Langlands.Representation.Aubert.General.JacquetColimits
import Langlands.Representation.Aubert.General.AlternatingOperator
import Langlands.Representation.Category.ExactInclusion
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers

/-! # Small colimits under normalized parabolic induction

Published actual short-exactness gives preservation of finite colimits.
Together with the compact-quotient coproduct result this gives all small colimits.
-/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

universe uG uV

namespace Langlands.Aubert.General

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U : Subgroup G}
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))

instance normalizedInductionFunctor_additive :
    (normalizedInductionFunctor.{uG, uV} h hU).Additive where
  map_add {_ _} _ _ := by
    apply ObjectProperty.hom_ext
    ext v
    rfl

/-- Actual short-exactness supplies the categorical finite-colimit property. -/
theorem normalizedInductionFunctor_preservesFiniteColimits [T2Space G]
    (hcof : CompactOpenCofinal G) (hP : IsClosed (P : Set G))
    (hproj : Continuous h.projection) :
    PreservesFiniteColimits (normalizedInductionFunctor.{uG, uV} h hU) := by
  let I := normalizedInductionFunctor.{uG, uV} h hU
  apply ((Functor.preservesFiniteColimits_tfae I).out 1 4).mp
  intro S hS
  have hSM := hS.map_of_exact (SmoothRep.forgetToModule M)
  have hactual : SmoothRep.IsShortExact (SmoothRep.hom S.f) (SmoothRep.hom S.g) :=
    ⟨(SmoothRep.mono_iff_injective S.f).mp hS.mono_f,
      (SmoothRep.epi_iff_surjective S.g).mp hS.epi_g,
      (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mp hSM.exact⟩
  have hI := normalizedInductionFunctor_map_isShortExact hcof h hU hP hproj S.f S.g hactual
  refine ⟨?_, (SmoothRep.epi_iff_surjective _).mpr hI.2.1⟩
  apply (SmoothRep.forgetToModule G).reflects_exact_of_faithful
  exact (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mpr hI.2.2

/-- Compact quotient and the published exactness hypotheses give preservation
of colimits of diagrams at the original carrier size. -/
theorem normalizedInductionFunctor_preservesColimits [T2Space G]
    (hcof : CompactOpenCofinal G) (hP : IsClosed (P : Set G))
    (hproj : Continuous h.projection) [CompactSpace (Induction.LeftQuotient P)] :
    PreservesColimitsOfSize.{uV, uV} (normalizedInductionFunctor.{uG, uV} h hU) := by
  classical
  have : HasCoproducts.{uV} (SmoothRep.{0, uG, uV} ℂ M) :=
    hasCoproducts_of_colimit_cofans
      (fun A => SmoothRep.directSumCofan.{uG, uV, 0} A)
      (fun A => SmoothRep.directSumIsColimit.{uG, uV, 0} A)
  have := normalizedInductionFunctor_preservesFiniteColimits.{uG, uV} h hU hcof hP hproj
  have (J : Type uV) : PreservesColimitsOfShape (Discrete J)
      (normalizedInductionFunctor.{uG, uV} h hU) :=
    normalizedInductionFunctor_preservesCoproducts.{uG, uV, 0} h hU
  exact preservesColimits_of_preservesCoequalizers_and_coproducts _

/-- Transport an explicit small colimit cocone through normalized induction. -/
def normalizedInductionColimitCocone [T2Space G]
    (hcof : CompactOpenCofinal G) (hP : IsClosed (P : Set G))
    (hproj : Continuous h.projection) [CompactSpace (Induction.LeftQuotient P)]
    {J : Type uV} [Category.{uV} J]
    {F : J ⥤ SmoothRep.{0, uG, uV} ℂ M} (c : ColimitCocone F) :
    ColimitCocone (F ⋙ normalizedInductionFunctor.{uG, uV} h hU) := by
  have := normalizedInductionFunctor_preservesColimits.{uG, uV} h hU hcof hP hproj
  exact ⟨(normalizedInductionFunctor h hU).mapCocone c.cocone,
    isColimitOfPreserves (normalizedInductionFunctor h hU) c.isColimit⟩

end Langlands.Aubert.General
