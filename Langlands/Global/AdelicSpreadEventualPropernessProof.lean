import Langlands.Global.AdelicSpreadEventualPropernessStatement
import Langlands.Global.AdelicSIntegersColimitProof
import Langlands.Global.AdelicSIntegersNoetherianProof
import Langlands.AlgebraicGeometry.SchemeFilteredProperProof
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Properness after an actual arithmetic enlargement -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry

namespace Langlands.Global

open Langlands.AlgebraicGeometry.AffineLimit
open Langlands.AlgebraicGeometry.SchemeLimitModel

set_option backward.isDefEq.respectTransparency false in
/-- The two orders of the actual pullback give the same properness property. -/
private theorem isProper_baseChangeMap_iff
    {S T : Scheme.{u}} (X Y : Over S) (f : X ⟶ Y) (p : T ⟶ S) :
    IsProper (baseChangeMap X.hom Y.hom f.left (Over.w f) p) ↔
      IsProper ((Over.pullback p).map f).left := by
  have h :
      baseChangeMap X.hom Y.hom f.left (Over.w f) p ≫
        (pullbackSymmetry p Y.hom).hom =
      (pullbackSymmetry p X.hom).hom ≫ ((Over.pullback p).map f).left := by
    simp only [baseChangeMap, Over.pullback_map_left]
    apply pullback.hom_ext <;> simp [Category.assoc]
  calc
    IsProper (baseChangeMap X.hom Y.hom f.left (Over.w f) p) ↔
        IsProper (baseChangeMap X.hom Y.hom f.left (Over.w f) p ≫
          (pullbackSymmetry p Y.hom).hom) :=
      (MorphismProperty.cancel_right_of_respectsIso
        (P := @IsProper) _ (pullbackSymmetry p Y.hom).hom).symm
    _ ↔ IsProper ((pullbackSymmetry p X.hom).hom ≫
        ((Over.pullback p).map f).left) := by rw [h]
    _ ↔ IsProper ((Over.pullback p).map f).left :=
      MorphismProperty.cancel_left_of_respectsIso
        (P := @IsProper) (pullbackSymmetry p X.hom).hom _

/-- Finite type over a noetherian initial base supplies the hypotheses of
relative properness descent, including for nonseparated models. -/
private theorem finiteTypeModels_proper_iff_stage
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (A : J ⥤ CommAlgCat.{u} R) (c : Cocone A) (hc : IsColimit c)
    (X Y : Over (Spec (CommRingCat.of R)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] (f : X ⟶ Y) :
    IsProper ((Over.pullback (spectrumBaseMap R A c)).map f).left ↔
      ∃ j : J, IsProper
        ((Over.pullback ((spectrumStructure R A).app (op j))).map f).left := by
  let : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  let : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  have : LocallyOfFinitePresentation (f.left ≫ Y.hom) := by
    rw [Over.w f]
    infer_instance
  have : QuasiCompact (f.left ≫ Y.hom) := by
    rw [Over.w f]
    infer_instance
  have : QuasiSeparated (f.left ≫ Y.hom) := by
    rw [Over.w f]
    infer_instance
  have : LocallyOfFinitePresentation f.left :=
    Langlands.AlgebraicGeometry.locallyOfFinitePresentation_of_comp f.left Y.hom
  have : QuasiCompact f.left := QuasiCompact.of_comp f.left Y.hom
  have : QuasiSeparated f.left := QuasiSeparated.of_comp f.left Y.hom
  simpa only [isProper_baseChangeMap_iff] using
    spectrumProperDescent R A c hc X Y f

/-- The original function field is the colimit of its literal integer stages. -/
theorem curvePlaceSpreadEventualProperness :
    CurvePlaceSpreadEventualPropernessStatement.{u} := by
  intro k F _ _ _ _ _ _ _ S X Y _ _ _ _ f
  let : IsNoetherianRing (curvePlaceSIntegers k F S) :=
    (adelicSIntegersNoetherian.1 k F S).1
  exact finiteTypeModels_proper_iff_stage (curvePlaceSIntegers k F S)
    (curvePlaceSIntegersOverDiagram k F S) (curvePlaceSIntegersOverCocone k F S)
    (curvePlaceSIntegersOverIsColimit k F S) X Y f

/-- The same specialization retains the original number field and integer rings. -/
theorem numberFieldSpreadEventualProperness :
    NumberFieldSpreadEventualPropernessStatement.{u} := by
  intro K _ _ S X Y _ _ _ _ f
  let : IsNoetherianRing ((S : Set (FinitePlace K)).integer K) :=
    (adelicSIntegersNoetherian.2 K S).1
  exact finiteTypeModels_proper_iff_stage ((S : Set (FinitePlace K)).integer K)
    (numberFieldSIntegersOverDiagram K S) (numberFieldSIntegersOverCocone K S)
    (numberFieldSIntegersOverIsColimit K S) X Y f

/-- Both actual arithmetic forms of eventual properness. -/
theorem adelicSpreadEventualProperness : AdelicSpreadEventualPropernessStatement.{u} :=
  ⟨curvePlaceSpreadEventualProperness, numberFieldSpreadEventualProperness⟩

end Langlands.Global
