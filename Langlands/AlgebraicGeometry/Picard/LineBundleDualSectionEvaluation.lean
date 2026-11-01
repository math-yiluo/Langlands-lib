import Langlands.AlgebraicGeometry.Picard.LineBundleDualEvaluation
import Langlands.AlgebraicGeometry.Modules.PullbackTensorProof
import Langlands.AlgebraicGeometry.Modules.SectionLocusComparison

/-! # Evaluation against a global section of a dual line bundle -/

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.LineBundle

open Langlands.Scheme.Modules Langlands.SchemeModule

variable {X : Scheme.{u}}

/-- The internal dual, packaged as an actual line bundle. -/
def dual (D : LineBundle X) : LineBundle X :=
  ⟨Langlands.Scheme.Modules.dual D.obj, isLocallyFreeRankOne_dual D.property⟩

/-- The map to the structure module obtained by evaluating against a dual section. -/
def evalSection (D : LineBundle X) (t : GlobalSections D.dual.obj) :
    D.obj ⟶ SheafOfModules.unit X.ringCatSheaf :=
  (tensorRightUnitor D.obj).inv ≫
    tensorMap (𝟙 D.obj) (sectionHom D.dual.obj t) ≫ dualTensorEval D.obj

/-- Evaluation against a dual section is an isomorphism on any open on which that
section trivializes the dual bundle. -/
theorem isIso_restrict_evalSection (D : LineBundle X) (t : GlobalSections D.dual.obj)
    (U : X.Opens) (hU : U ≤ trivializationOpen D.dual.obj t) :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map (D.evalSection t)) := by
  let P := Scheme.Modules.pullback U.ι
  let c := pullbackTensorComparison U.ι
  have : IsIso c := pullbackTensorComparisonIsIso U.ι
  have htR : IsIso ((Scheme.Modules.restrictFunctor U.ι).map
      (sectionHom D.dual.obj t)) :=
    (maximalTrivialization X D.dual.obj t U).mpr hU
  have htP : IsIso (P.map (sectionHom D.dual.obj t)) :=
    (NatIso.isIso_map_iff (Scheme.Modules.restrictFunctorIsoPullback U.ι) _).mp htR
  have htensor : IsIso
      (tensorMap (P.map (𝟙 D.obj)) (P.map (sectionHom D.dual.obj t))) :=
    inferInstanceAs (IsIso ((tensorFunctor U.toScheme).mapIso
      ((asIso (P.map (𝟙 D.obj))).prod (asIso (P.map (sectionHom D.dual.obj t))))).hom)
  have hnat : P.map (tensorMap (𝟙 D.obj) (sectionHom D.dual.obj t)) ≫
        c.app (D.obj, D.dual.obj) =
      c.app (D.obj, structureSheaf X) ≫
        tensorMap (P.map (𝟙 D.obj)) (P.map (sectionHom D.dual.obj t)) :=
    c.naturality (X := (D.obj, structureSheaf X)) (Y := (D.obj, D.dual.obj))
      (𝟙 D.obj, sectionHom D.dual.obj t)
  have hmap : IsIso (P.map (tensorMap (𝟙 D.obj) (sectionHom D.dual.obj t))) := by
    apply (isIso_comp_right_iff _ (c.app (D.obj, D.dual.obj))).mp
    rw [hnat]
    infer_instance
  have : IsIso (dualTensorEval D.obj) := isIso_dualTensorEval D.property
  have hP : IsIso (P.map (D.evalSection t)) := by
    dsimp only [evalSection]
    rw [Functor.map_comp, Functor.map_comp]
    infer_instance
  exact (NatIso.isIso_map_iff (Scheme.Modules.restrictFunctorIsoPullback U.ι) _).mpr hP

/-- At every point where the dual section generates, evaluation against it is a
stalk isomorphism. -/
theorem isIso_stalk_evalSection_of_mem (D : LineBundle X) (t : GlobalSections D.dual.obj)
    {x : X} (hx : x ∈ trivializationOpen D.dual.obj t) :
    IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map
      ((Scheme.Modules.toPresheaf X).map (D.evalSection t))) := by
  let U := trivializationOpen D.dual.obj t
  have : IsIso ((Scheme.Modules.restrictFunctor U.ι).map (D.evalSection t)) :=
    D.isIso_restrict_evalSection t U le_rfl
  exact (isIso_stalk_restrict_iff (D.evalSection t) U ⟨x, hx⟩).mp (by infer_instance)

end Langlands.AlgebraicGeometry.Picard.LineBundle
