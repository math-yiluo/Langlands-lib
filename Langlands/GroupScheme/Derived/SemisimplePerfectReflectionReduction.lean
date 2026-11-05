import Langlands.GroupScheme.Derived.SemisimplePerfectGeneration
import Langlands.GroupScheme.Derived.SemisimpleReflectionReduction
import Langlands.GroupScheme.Rational.RootReflectionExistenceStatement

/-! # Semisimple perfectness from actual reflections and torus generation -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The structural reduction of perfectness requires only actual integral
reflection existence and finite torus generation. -/
def SemisimplePerfectReflectionReductionStatement : Prop :=
  RelativeRootReflectionExistenceStatement.{u} →
    ReductiveFiniteTorusGenerationStatement.{u} →
      SemisimplePerfectStatement.{u}

/-- Actual integral reflections give the needed maximal-torus containment
in semisimple groups, without root-reducedness or character-complement inputs. -/
theorem algebraicallyClosedSemisimpleMaximalTorusDerived_of_reflectionExistence
    (hreflect : RelativeRootReflectionExistenceStatement.{u}) :
    AlgebraicallyClosedSemisimpleMaximalTorusDerivedStatement.{u} := by
  intro k _ _ G hG T i hi
  have := hG.isConnectedReductive.isAffineHom
  have : IsClosedImmersion i.hom.hom.left := hi.2.1
  have hT := hi.1.isSplitTorus_of_finiteGaloisSplitting torusFiniteGaloisSplitting
  obtain ⟨D, _⟩ := hreflect k G hG.isConnectedReductive T i (hi.isMaximalSplitTorus hT)
  obtain ⟨J, _, P, hP, hfinite⟩ := D.exists_semisimple_rootDatum hG hT hi.2.1
  let := hfinite
  exact hP.range_le_derivedSubgroup_of_finite_corootIndex i hT

/-- Proof of the conditional reflection-and-generation reduction. Neither
structural premise is asserted unconditionally here. -/
theorem semisimplePerfect_of_reflectionExistence_of_torusGeneration :
    SemisimplePerfectReflectionReductionStatement.{u} := by
  intro hreflect hgen
  exact semisimplePerfect_of_maximalTorusDerived_of_torusGeneration
    (algebraicallyClosedSemisimpleMaximalTorusDerived_of_reflectionExistence hreflect) hgen

end Langlands.GroupScheme
