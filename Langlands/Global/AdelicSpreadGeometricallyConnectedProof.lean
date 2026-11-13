import Langlands.Global.AdelicSpreadGeometricallyConnectedStatement
import Langlands.Global.AdelicSpreadEventualSmoothFiberGeometryProof
import Langlands.Global.AdelicSpreadSmoothExistenceProof
import Langlands.AlgebraicGeometry.ConstructibleAffineLimit
import Langlands.AlgebraicGeometry.GeometricallyConnectedFiberConstructibilityProof
import Langlands.AlgebraicGeometry.SchemeLimitFiberLoci

/-! # Geometric connectedness at actual arithmetic integer levels -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open Set Topology CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry

namespace Langlands.Global

open Langlands.AlgebraicGeometry.AffineLimit
open Langlands.AlgebraicGeometry.EtaleEquivalenceRelation.Action.TargetLimit
open Langlands.AlgebraicGeometry.SchemeLimitModel
open Langlands.AlgebraicGeometry.SchemeLimitModel.Geometry
open Langlands.AlgebraicGeometry.SchemeFiberGeometry

/-- The actual geometric-connectedness locus is constructible at each
stage, so fullness at the limit is detected at one finite stage. -/
private theorem relativeGeometricallyConnectedDescent
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    {S X Y : Scheme.{u}} (D : I ⥤ Scheme.{u})
    (t : D ⟶ (Functor.const I).obj S)
    [∀ {i j} (r : i ⟶ j), IsAffineHom (D.map r)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    (a : X ⟶ S) (b : Y ⟶ S) (f : X ⟶ Y) (w : f ≫ b = a)
    [QuasiCompact b] [QuasiSeparated b]
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (c : Cone D) (hc : IsLimit c) (p : c.pt ⟶ S)
    (hp : ∀ i, c.π.app i ≫ t.app i = p) :
    GeometricallyConnected (baseChangeMap a b f w p) ↔
      ∃ i, GeometricallyConnected (baseChangeMap a b f w (t.app i)) := by
  have hlevel : ∀ i, IsConstructible
      (geometricallyConnectedFiberLocus (baseChangeMap a b f w (t.app i))) := by
    intro i
    have : LocallyOfFinitePresentation (baseChangeMap a b f w (t.app i)) :=
      MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation)
        (baseChangeMap_cartesian a b f w (t.app i)).flip inferInstance
    have : QuasiCompact (baseChangeMap a b f w (t.app i)) :=
      MorphismProperty.of_isPullback (P := @QuasiCompact)
        (baseChangeMap_cartesian a b f w (t.app i)).flip inferInstance
    have : QuasiSeparated (baseChangeMap a b f w (t.app i)) :=
      MorphismProperty.of_isPullback (P := @QuasiSeparated)
        (baseChangeMap_cartesian a b f w (t.app i)).flip inferInstance
    have : QuasiSeparatedSpace (pullback (t.app i) b : Scheme.{u}) :=
      quasiSeparatedSpace_of_quasiSeparated (pullback.fst (t.app i) b)
    exact isConstructible_geometricallyConnectedFiberLocus_of_localConstructibility
      geometricallyConnectedFiberLocalConstructibility _
  constructor
  · intro H
    obtain ⟨i⟩ := IsCofiltered.nonempty (C := I)
    have H' := (geometricallyConnectedFiberLocus_eq_univ_iff _).mpr H
    rw [geometricallyConnectedFiberLocus_cone a b f w D t c p hp i] at H'
    obtain ⟨j, r, hj⟩ := exists_map_preimage_eq_univ_of_isConstructible
      (diagram D t b) (cone D t b c p hp) (isLimitCone D t b c p hp hc)
      i _ (hlevel i) H'
    refine ⟨j, (geometricallyConnectedFiberLocus_eq_univ_iff _).mp ?_⟩
    rw [geometricallyConnectedFiberLocus_baseChange
      (morphismDiagram_cartesian a b f w D t r).flip]
    exact hj
  · rintro ⟨i, hi⟩
    apply (geometricallyConnectedFiberLocus_eq_univ_iff _).mp
    rw [geometricallyConnectedFiberLocus_cone a b f w D t c p hp i,
      (geometricallyConnectedFiberLocus_eq_univ_iff _).mpr hi, preimage_univ]

/-- Finite-type models over a Noetherian initial ring meet the general
constructible-locus theorem's finite-presentation and qcqs hypotheses. -/
private theorem finiteTypeModels_geometricallyConnected_iff_stage
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (A : J ⥤ CommAlgCat.{u} R) (c : Cocone A) (hc : IsColimit c)
    (X Y : Over (Spec (CommRingCat.of R)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] (f : X ⟶ Y) :
    GeometricallyConnected ((Over.pullback (spectrumBaseMap R A c)).map f).left ↔
      ∃ j : J, GeometricallyConnected
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
  have hdesc := relativeGeometricallyConnectedDescent (spectrumDiagram R A)
    (spectrumStructure R A) X.hom Y.hom f.left (Over.w f)
    (spectrumCone R A c) (spectrumConeIsLimit R A c hc) (spectrumBaseMap R A c)
    (spectrumCone_compat R A c)
  simp only [property_baseChangeMap_iff @GeometricallyConnected X Y f] at hdesc
  exact hdesc.trans ⟨fun ⟨j, h⟩ ↦ ⟨j.unop, h⟩, fun ⟨j, h⟩ ↦ ⟨op j, h⟩⟩

/-- Actual function-field integer rings detect geometric connectedness. -/
theorem curvePlaceSpreadEventualGeometricallyConnected :
    CurvePlaceSpreadEventualPropertyStatement.{u} @GeometricallyConnected := by
  intro k F _ _ _ _ _ _ _ S X Y _ _ _ _ f
  let : IsNoetherianRing (curvePlaceSIntegers k F S) :=
    (adelicSIntegersNoetherian.1 k F S).1
  exact finiteTypeModels_geometricallyConnected_iff_stage (curvePlaceSIntegers k F S)
    (curvePlaceSIntegersOverDiagram k F S) (curvePlaceSIntegersOverCocone k F S)
    (curvePlaceSIntegersOverIsColimit k F S) X Y f

/-- The same detection on the original number-field integer rings. -/
theorem numberFieldSpreadEventualGeometricallyConnected :
    NumberFieldSpreadEventualPropertyStatement.{u} @GeometricallyConnected := by
  intro K _ _ S X Y _ _ _ _ f
  let : IsNoetherianRing ((S : Set (FinitePlace K)).integer K) :=
    (adelicSIntegersNoetherian.2 K S).1
  exact finiteTypeModels_geometricallyConnected_iff_stage
    ((S : Set (FinitePlace K)).integer K)
    (numberFieldSIntegersOverDiagram K S) (numberFieldSIntegersOverCocone K S)
    (numberFieldSIntegersOverIsColimit K S) X Y f

/-- Stable properties detected separately are realized at one common
filtered stage by the actual cartesian transition squares. -/
private theorem spectrumIntersection_iff_stage
    (P Q : MorphismProperty Scheme.{u})
    [P.RespectsIso] [Q.RespectsIso] [P.IsStableUnderBaseChange] [Q.IsStableUnderBaseChange]
    (R : Type u) [CommRing R]
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (A : J ⥤ CommAlgCat.{u} R) (c : Cocone A)
    (X Y : Over (Spec (CommRingCat.of R))) (f : X ⟶ Y)
    (hP : P ((Over.pullback (spectrumBaseMap R A c)).map f).left ↔
      ∃ j : J, P ((Over.pullback ((spectrumStructure R A).app (op j))).map f).left)
    (hQ : Q ((Over.pullback (spectrumBaseMap R A c)).map f).left ↔
      ∃ j : J, Q ((Over.pullback ((spectrumStructure R A).app (op j))).map f).left) :
    (P ⊓ Q) ((Over.pullback (spectrumBaseMap R A c)).map f).left ↔
      ∃ j : J, (P ⊓ Q)
        ((Over.pullback ((spectrumStructure R A).app (op j))).map f).left := by
  constructor
  · rintro ⟨hp, hq⟩
    obtain ⟨i, hi⟩ := hP.mp hp
    obtain ⟨j, hj⟩ := hQ.mp hq
    refine ⟨IsFiltered.max i j, ?_, ?_⟩
    · apply (property_baseChangeMap_iff P X Y f _).mp
      exact MorphismProperty.of_isPullback (P := P)
        (morphismDiagram_cartesian X.hom Y.hom f.left (Over.w f)
          (spectrumDiagram R A) (spectrumStructure R A)
          (IsFiltered.leftToMax i j).op).flip
        ((property_baseChangeMap_iff P X Y f _).mpr hi)
    · apply (property_baseChangeMap_iff Q X Y f _).mp
      exact MorphismProperty.of_isPullback (P := Q)
        (morphismDiagram_cartesian X.hom Y.hom f.left (Over.w f)
          (spectrumDiagram R A) (spectrumStructure R A)
          (IsFiltered.rightToMax i j).op).flip
        ((property_baseChangeMap_iff Q X Y f _).mpr hj)
  · rintro ⟨j, hp, hq⟩
    exact ⟨hP.mpr ⟨j, hp⟩, hQ.mpr ⟨j, hq⟩⟩

/-- Smoothness and geometric connectedness hold at one actual integer level. -/
theorem curvePlaceSpreadEventualSmoothGeometricallyConnected :
    CurvePlaceSpreadEventualPropertyStatement.{u}
      (@Smooth ⊓ @GeometricallyConnected) := by
  intro k F _ _ _ _ _ _ _ S X Y _ _ _ _ f
  exact spectrumIntersection_iff_stage @Smooth @GeometricallyConnected
    (curvePlaceSIntegers k F S)
    (curvePlaceSIntegersOverDiagram k F S) (curvePlaceSIntegersOverCocone k F S)
    X Y f (curvePlaceSpreadEventualSmoothness k F S X Y f)
    (curvePlaceSpreadEventualGeometricallyConnected k F S X Y f)

/-- Both properties hold at one actual number-field integer level. -/
theorem numberFieldSpreadEventualSmoothGeometricallyConnected :
    NumberFieldSpreadEventualPropertyStatement.{u}
      (@Smooth ⊓ @GeometricallyConnected) := by
  intro K _ _ S X Y _ _ _ _ f
  exact spectrumIntersection_iff_stage @Smooth @GeometricallyConnected
    ((S : Set (FinitePlace K)).integer K)
    (numberFieldSIntegersOverDiagram K S) (numberFieldSIntegersOverCocone K S)
    X Y f (numberFieldSpreadEventualSmoothness K S X Y f)
    (numberFieldSpreadEventualGeometricallyConnected K S X Y f)

/-- Compatible smooth geometrically connected models, without fixed dimension. -/
theorem curvePlaceSpreadGeometricallyConnected :
    CurvePlaceSpreadGeometricallyConnectedStatement.{u} :=
  ⟨curvePlaceSpreadEventualGeometricallyConnected,
    curvePlaceSpreadEventualSmoothGeometricallyConnected,
    curvePlaceSpreadMorphismPropertyExistence _
      curvePlaceSpreadEventualSmoothGeometricallyConnected⟩

/-- The compatible-model conclusion for the original number field. -/
theorem numberFieldSpreadGeometricallyConnected :
    NumberFieldSpreadGeometricallyConnectedStatement.{u} :=
  ⟨numberFieldSpreadEventualGeometricallyConnected,
    numberFieldSpreadEventualSmoothGeometricallyConnected,
    numberFieldSpreadMorphismPropertyExistence _
      numberFieldSpreadEventualSmoothGeometricallyConnected⟩

/-- Both arithmetic branches with coherent actual generic fibres. -/
theorem adelicSpreadGeometricallyConnected :
    AdelicSpreadGeometricallyConnectedStatement.{u} :=
  ⟨curvePlaceSpreadGeometricallyConnected, numberFieldSpreadGeometricallyConnected⟩

end Langlands.Global
