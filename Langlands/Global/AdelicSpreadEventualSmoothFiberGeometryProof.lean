import Langlands.Global.AdelicSpreadEventualSmoothFiberGeometryStatement
import Langlands.Global.AdelicSIntegersColimitProof
import Langlands.Global.AdelicSIntegersNoetherianProof
import Langlands.AlgebraicGeometry.SchemeFilteredRelativePropertyProof
import Langlands.AlgebraicGeometry.SchemeFilteredFiberGeometryProof
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-! # Eventual smoothness and fibre geometry over the actual integer rings -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry

namespace Langlands.Global

open Langlands.AlgebraicGeometry.AffineLimit
open Langlands.AlgebraicGeometry.SchemeLimitModel
open Langlands.AlgebraicGeometry.SchemeLimitModel.Geometry
open Langlands.AlgebraicGeometry.SchemeFiberGeometry

/-- The algebra/ring forgetful functor preserves these filtered colimits,
via the usual equivalence with rings under the fixed base. -/
private instance commAlgForget_preservesColimitsOfShape
    (R : Type u) [CommRing R]
    {J : Type u} [SmallCategory J] [IsFiltered J] :
    PreservesColimitsOfShape J (forget₂ (CommAlgCat.{u} R) CommRingCat.{u}) := by
  change PreservesColimitsOfShape J
    ((commAlgCatEquivUnder (CommRingCat.of R)).functor ⋙
      Under.forget (CommRingCat.of R))
  infer_instance

/-- Pullback symmetry identifies the two actual base-change conventions. -/
private theorem property_baseChangeMap_iff
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {S T : Scheme.{u}} (X Y : Over S) (f : X ⟶ Y) (p : T ⟶ S) :
    P (baseChangeMap X.hom Y.hom f.left (Over.w f) p) ↔
      P ((Over.pullback p).map f).left := by
  have h :
      baseChangeMap X.hom Y.hom f.left (Over.w f) p ≫
        (pullbackSymmetry p Y.hom).hom =
      (pullbackSymmetry p X.hom).hom ≫ ((Over.pullback p).map f).left := by
    simp only [baseChangeMap, Over.pullback_map_left]
    apply pullback.hom_ext <;> simp [Category.assoc]
  calc
    P (baseChangeMap X.hom Y.hom f.left (Over.w f) p) ↔
        P (baseChangeMap X.hom Y.hom f.left (Over.w f) p ≫
          (pullbackSymmetry p Y.hom).hom) :=
      (MorphismProperty.cancel_right_of_respectsIso
        (P := P) _ (pullbackSymmetry p Y.hom).hom).symm
    _ ↔ P ((pullbackSymmetry p X.hom).hom ≫
        ((Over.pullback p).map f).left) := by rw [h]
    _ ↔ P ((Over.pullback p).map f).left :=
      MorphismProperty.cancel_left_of_respectsIso
        (P := P) (pullbackSymmetry p X.hom).hom _

/-- Noetherianity of the initial ring turns the supplied finite-type models
into the finitely presented morphism needed by smoothness descent. -/
private theorem finiteTypeModels_smooth_iff_stage
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (A : J ⥤ CommAlgCat.{u} R) (c : Cocone A) (hc : IsColimit c)
    (X Y : Over (Spec (CommRingCat.of R)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] (f : X ⟶ Y) :
    Smooth ((Over.pullback (spectrumBaseMap R A c)).map f).left ↔
      ∃ j : J, Smooth
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
  simpa only [property_baseChangeMap_iff @Smooth X Y f] using
    spectrumRelativeSmoothFlatDescent.1 R A c hc X Y f

/-- Smoothness is detected on an actual function-field integer superlevel. -/
theorem curvePlaceSpreadEventualSmoothness :
    CurvePlaceSpreadEventualPropertyStatement.{u} @Smooth := by
  intro k F _ _ _ _ _ _ _ S X Y _ _ _ _ f
  let : IsNoetherianRing (curvePlaceSIntegers k F S) :=
    (adelicSIntegersNoetherian.1 k F S).1
  exact finiteTypeModels_smooth_iff_stage (curvePlaceSIntegers k F S)
    (curvePlaceSIntegersOverDiagram k F S) (curvePlaceSIntegersOverCocone k F S)
    (curvePlaceSIntegersOverIsColimit k F S) X Y f

/-- Smoothness is detected on an actual number-field integer superlevel. -/
theorem numberFieldSpreadEventualSmoothness :
    NumberFieldSpreadEventualPropertyStatement.{u} @Smooth := by
  intro K _ _ S X Y _ _ _ _ f
  let : IsNoetherianRing ((S : Set (FinitePlace K)).integer K) :=
    (adelicSIntegersNoetherian.2 K S).1
  exact finiteTypeModels_smooth_iff_stage ((S : Set (FinitePlace K)).integer K)
    (numberFieldSIntegersOverDiagram K S) (numberFieldSIntegersOverCocone K S)
    (numberFieldSIntegersOverIsColimit K S) X Y f

/-- Forgetting the algebra structure retains the original rings and their
actual transitions out of the initial function-field integer ring. -/
theorem curvePlaceSpreadEventualFiberGeometry (d : ℕ) :
    CurvePlaceSpreadEventualPropertyStatement.{u}
      (NonemptyGeometricallyConnectedPureDimensionFibers d) := by
  intro k F _ _ _ _ _ _ _ S X Y _ _ _ _ f
  let : IsNoetherianRing (curvePlaceSIntegers k F S) :=
    (adelicSIntegersNoetherian.1 k F S).1
  let : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  let : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  have : LocallyOfFinitePresentation X.hom := inferInstance
  have : LocallyOfFinitePresentation Y.hom := inferInstance
  have : QuasiSeparated X.hom := inferInstance
  have : QuasiSeparated Y.hom := inferInstance
  let A := curvePlaceSIntegersOverDiagram k F S
  let U := forget₂ (CommAlgCat (curvePlaceSIntegers k F S)) CommRingCat
  let c := U.mapCocone (curvePlaceSIntegersOverCocone k F S)
  let j₀ : AdelicLevelIndexAbove S := ⟨S, Finset.Subset.refl S⟩
  have hc : IsColimit c :=
    isColimitOfPreserves U (curvePlaceSIntegersOverIsColimit k F S)
  have hdesc := finitePresentationInitialRingFiberGeometryDescent d
    (A ⋙ U) c hc j₀ X Y f
  simp only [property_baseChangeMap_iff
    (NonemptyGeometricallyConnectedPureDimensionFibers d) X Y f] at hdesc
  constructor
  · intro h
    obtain ⟨j, hj⟩ := hdesc.mp h
    exact ⟨j.right, hj⟩
  · rintro ⟨T, hT⟩
    exact hdesc.mpr ⟨Under.mk (homOfLE (show j₀ ≤ T from T.property)), hT⟩

/-- The same initial-ring argument uses the original number-field integers. -/
theorem numberFieldSpreadEventualFiberGeometry (d : ℕ) :
    NumberFieldSpreadEventualPropertyStatement.{u}
      (NonemptyGeometricallyConnectedPureDimensionFibers d) := by
  intro K _ _ S X Y _ _ _ _ f
  let : IsNoetherianRing ((S : Set (FinitePlace K)).integer K) :=
    (adelicSIntegersNoetherian.2 K S).1
  let : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  let : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  have : LocallyOfFinitePresentation X.hom := inferInstance
  have : LocallyOfFinitePresentation Y.hom := inferInstance
  have : QuasiSeparated X.hom := inferInstance
  have : QuasiSeparated Y.hom := inferInstance
  let A := numberFieldSIntegersOverDiagram K S
  let U := forget₂ (CommAlgCat ((S : Set (FinitePlace K)).integer K)) CommRingCat
  let c := U.mapCocone (numberFieldSIntegersOverCocone K S)
  let j₀ : AdelicLevelIndexAbove S := ⟨S, Finset.Subset.refl S⟩
  have hc : IsColimit c :=
    isColimitOfPreserves U (numberFieldSIntegersOverIsColimit K S)
  have hdesc := finitePresentationInitialRingFiberGeometryDescent d
    (A ⋙ U) c hc j₀ X Y f
  simp only [property_baseChangeMap_iff
    (NonemptyGeometricallyConnectedPureDimensionFibers d) X Y f] at hdesc
  constructor
  · intro h
    obtain ⟨j, hj⟩ := hdesc.mp h
    exact ⟨j.right, hj⟩
  · rintro ⟨T, hT⟩
    exact hdesc.mpr ⟨Under.mk (homOfLE (show j₀ ≤ T from T.property)), hT⟩

/-- Two separately detected properties can be realized at one stage: the
actual cartesian squares preserve smoothness and the full fibre locus. -/
private theorem spectrumSmoothFiberGeometry_iff_stage
    (R : Type u) [CommRing R]
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (A : J ⥤ CommAlgCat.{u} R) (c : Cocone A)
    (X Y : Over (Spec (CommRingCat.of R))) (f : X ⟶ Y)
    [LocallyOfFiniteType f.left] (d : ℕ)
    (hsmooth :
      Smooth ((Over.pullback (spectrumBaseMap R A c)).map f).left ↔
        ∃ j : J, Smooth
          ((Over.pullback ((spectrumStructure R A).app (op j))).map f).left)
    (hgeometry :
      NonemptyGeometricallyConnectedPureDimensionFibers d
        ((Over.pullback (spectrumBaseMap R A c)).map f).left ↔
        ∃ j : J, NonemptyGeometricallyConnectedPureDimensionFibers d
          ((Over.pullback ((spectrumStructure R A).app (op j))).map f).left) :
    (@Smooth ⊓ NonemptyGeometricallyConnectedPureDimensionFibers d :
        MorphismProperty Scheme.{u})
        ((Over.pullback (spectrumBaseMap R A c)).map f).left ↔
      ∃ j : J, (@Smooth ⊓ NonemptyGeometricallyConnectedPureDimensionFibers d :
        MorphismProperty Scheme.{u})
        ((Over.pullback ((spectrumStructure R A).app (op j))).map f).left := by
  constructor
  · rintro ⟨hs, hg⟩
    obtain ⟨i, hi⟩ := hsmooth.mp hs
    obtain ⟨j, hj⟩ := hgeometry.mp hg
    refine ⟨IsFiltered.max i j, ?_, ?_⟩
    · apply (property_baseChangeMap_iff @Smooth X Y f _).mp
      exact MorphismProperty.of_isPullback (P := @Smooth)
        (morphismDiagram_cartesian X.hom Y.hom f.left (Over.w f)
          (spectrumDiagram R A) (spectrumStructure R A)
          (IsFiltered.leftToMax i j).op).flip
        ((property_baseChangeMap_iff @Smooth X Y f _).mpr hi)
    · apply (property_baseChangeMap_iff
        (NonemptyGeometricallyConnectedPureDimensionFibers d) X Y f _).mp
      have : LocallyOfFiniteType
          (baseChangeMap X.hom Y.hom f.left (Over.w f)
            ((spectrumStructure R A).app (op j))) :=
        MorphismProperty.of_isPullback (P := @LocallyOfFiniteType)
          (baseChangeMap_cartesian X.hom Y.hom f.left (Over.w f)
            ((spectrumStructure R A).app (op j))).flip inferInstance
      apply (nonemptyGeometricallyConnectedPureDimensionFiberLocus_eq_univ_iff d _).mp
      rw [nonemptyGeometricallyConnectedPureDimensionFiberLocus_baseChange
        (morphismDiagram_cartesian X.hom Y.hom f.left (Over.w f)
          (spectrumDiagram R A) (spectrumStructure R A)
          (IsFiltered.rightToMax i j).op).flip d,
        (nonemptyGeometricallyConnectedPureDimensionFiberLocus_eq_univ_iff d _).mpr
          ((property_baseChangeMap_iff
            (NonemptyGeometricallyConnectedPureDimensionFibers d) X Y f _).mpr hj),
        Set.preimage_univ]
  · rintro ⟨j, hs, hg⟩
    exact ⟨hsmooth.mpr ⟨j, hs⟩, hgeometry.mpr ⟨j, hg⟩⟩

/-- Smoothness and full fibre geometry hold at one actual function-field
integer superlevel. -/
theorem curvePlaceSpreadEventualSmoothFiberGeometry :
    CurvePlaceSpreadEventualSmoothFiberGeometryStatement.{u} := by
  refine ⟨curvePlaceSpreadEventualSmoothness, fun d =>
    ⟨curvePlaceSpreadEventualFiberGeometry d, ?_⟩⟩
  intro k F _ _ _ _ _ _ _ S X Y _ _ _ _ f
  have : LocallyOfFiniteType (f.left ≫ Y.hom) := by
    rw [Over.w f]
    infer_instance
  have : LocallyOfFiniteType f.left := locallyOfFiniteType_of_comp f.left Y.hom
  exact spectrumSmoothFiberGeometry_iff_stage (curvePlaceSIntegers k F S)
    (curvePlaceSIntegersOverDiagram k F S) (curvePlaceSIntegersOverCocone k F S)
    X Y f d (curvePlaceSpreadEventualSmoothness k F S X Y f)
    (curvePlaceSpreadEventualFiberGeometry d k F S X Y f)

/-- The same common-stage conclusion for the actual number-field integers. -/
theorem numberFieldSpreadEventualSmoothFiberGeometry :
    NumberFieldSpreadEventualSmoothFiberGeometryStatement.{u} := by
  refine ⟨numberFieldSpreadEventualSmoothness, fun d =>
    ⟨numberFieldSpreadEventualFiberGeometry d, ?_⟩⟩
  intro K _ _ S X Y _ _ _ _ f
  have : LocallyOfFiniteType (f.left ≫ Y.hom) := by
    rw [Over.w f]
    infer_instance
  have : LocallyOfFiniteType f.left := locallyOfFiniteType_of_comp f.left Y.hom
  exact spectrumSmoothFiberGeometry_iff_stage ((S : Set (FinitePlace K)).integer K)
    (numberFieldSIntegersOverDiagram K S) (numberFieldSIntegersOverCocone K S)
    X Y f d (numberFieldSpreadEventualSmoothness K S X Y f)
    (numberFieldSpreadEventualFiberGeometry d K S X Y f)

/-- Both arithmetic forms, including simultaneous smoothness and full
nonempty geometrically connected pure-dimensional fibres. -/
theorem adelicSpreadEventualSmoothFiberGeometry :
    AdelicSpreadEventualSmoothFiberGeometryStatement.{u} :=
  ⟨curvePlaceSpreadEventualSmoothFiberGeometry,
    numberFieldSpreadEventualSmoothFiberGeometry⟩

end Langlands.Global
