import Langlands.BruhatTits.IntegralModels.UnramifiedTorusNeutralSurjectivityStatement
import Langlands.BruhatTits.IntegralModels.UnramifiedTorusNormPresentationStatement
import Langlands.BruhatTits.IntegralModels.UnramifiedTorusIwahoriModelAssembly
import Langlands.GroupScheme.IntegralModel.CharacterValuationBound
import Langlands.GroupScheme.IntegralModel.SmoothHomExtensionProof

/-! # Reduction of the connected torus bound to neutral lifting and a norm presentation -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.LocalGalois.Separable
open Langlands.GroupScheme.GaloisPointComparison
open Langlands.Geometry.Building

namespace Langlands.BruhatTits.IntegralModels

/-- The three explicit prerequisites for the connected-model bound imply the
unchanged connected-model statement. -/
def UnramifiedTorusConnectedBoundAssemblyStatement : Prop :=
  UnramifiedTorusBoundedModelStatement.{u} →
  UnramifiedTorusNeutralSurjectivityStatement.{u} →
  UnramifiedTorusNormPresentationStatement.{u} →
  UnramifiedTorusConnectedBoundStatement.{u}

section Neutral

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G S : GroupScheme (Spec (CommRingCat.of K))}
  {W : IntegralModel R K S} (D : RelativeComponentModelData R K G)
  {n : S ⟶ G}

/-- A model homomorphism that factors through the supplied neutral model maps
the original integral-point image into the neutral integral-point image. -/
theorem map_integralPoints_le_supplied_neutral
    (φ : W.Hom D.full n) {y : W.group ⟶ D.neutral.group}
    (hy : y ≫ D.inclusion.hom = φ.hom) :
    W.integralPoints.map (rationalPoints.map n) ≤ D.neutral.integralPoints := by
  rw [← D.neutralPoints_eq]
  rintro _ ⟨g, ⟨w, rfl⟩, rfl⟩
  refine ⟨rationalPoints.map φ.hom w, ?_, ?_⟩
  · refine ⟨rationalPoints.map y w, ?_⟩
    rw [← hy]
    rfl
  · exact φ.integralPointMap_naturality w

end Neutral

set_option maxHeartbeats 1500000 in
/-- The connected-model bound for a supplied torus norm presentation. Its
remaining premises are bounded-model existence and neutral lifting. -/
theorem connectedBound_of_neutral_lifting_and_norm_presentation
    (hBdd : UnramifiedTorusBoundedModelStatement.{u})
    (hLift : UnramifiedTorusNeutralSurjectivityStatement.{u})
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (T : CommGroupScheme (Spec (CommRingCat.of (inertiaFixedField F))))
    [IsAffine T.X.left]
    (L : IntermediateField (inertiaFixedField F) (SeparableClosure F))
    [FiniteDimensional (inertiaFixedField F) L] [IsGalois (inertiaFixedField F) L]
    (hT : IsSplitTorus (baseChanged (inertiaFixedField F) L T.toGrp))
    (S : CommGroupScheme (Spec (CommRingCat.of (inertiaFixedField F))))
    [IsAffine S.X.left] (hS : IsTorus S.toGrp) (q : S.toGrp ⟶ T.toGrp)
    (hq : Surjective q.hom.hom.left) (hker : IsTorus (kernel q))
    (hNorm : (characterValuationKernel (fixedFieldValuation F) S.toGrp).map
        (rationalPoints.map q) ≤
      torusNormIwahori (inertiaFixedField F) L (intermediateValuation F L) T)
    (M : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) T.toGrp)
    (hM : M.IsSmooth) (hMgc : M.HasGeometricallyConnectedFibres) :
    M.integralPoints ≤
      torusNormIwahori (inertiaFixedField F) L (intermediateValuation F L) T := by
  obtain ⟨hdvr, hhens, hsep⟩ := fixedFieldIntegers_strictHenselian F
  have htorusT : IsTorus T.toGrp := ⟨L, inferInstance, inferInstance, hT⟩
  have : GeometricallyConnected T.toGrp.X.hom :=
    geometricallyConnected_of_isSplitTorus_baseChanged T.toGrp hT
  have : GeometricallyConnected S.toGrp.X.hom := by
    obtain ⟨E, hE, aE, hs⟩ := hS
    exact geometricallyConnected_of_isSplitTorus_baseChanged S.toGrp hs
  obtain ⟨MT, hMT, hMTpts⟩ := hBdd F T htorusT
  obtain ⟨MS, hMS, hMSpts⟩ := hBdd F S hS
  obtain ⟨DT, hDT, _⟩ := MT.exists_relativeComponentModelData hMT
  obtain ⟨DS, hDS, _⟩ := MS.exists_relativeComponentModelData hMS
  have hDTpts : DT.full.integralPoints =
      characterValuationKernel (fixedFieldValuation F) T.toGrp := by
    rw [hDT]
    exact hMTpts
  have hDSpts : DS.full.integralPoints =
      characterValuationKernel (fixedFieldValuation F) S.toGrp := by
    rw [hDS]
    exact hMSpts
  have hMpts : M.integralPoints ≤ DT.full.integralPoints := by
    rw [hDTpts]
    exact M.integralPoints_le_characterValuationKernel fun r => r.property
  obtain ⟨φ⟩ := IntegralModel.smoothHomExtension
    (fixedFieldIntegers F) (inertiaFixedField F) T.toGrp T.toGrp (𝟙 T.toGrp)
    M DT.full hM (fun g hg => by
      simpa only [rationalPoints.map_apply, Grp.id_hom_hom, Category.comp_id] using hMpts hg)
  have : GeometricallyConnected M.group.X.hom := hMgc
  obtain ⟨y, hy⟩ := DT.isRelativeComponent.exists_hom_lift φ.hom
  have hMneutral : M.integralPoints ≤ DT.neutral.integralPoints := by
    have h := map_integralPoints_le_supplied_neutral DT φ hy
    intro g hg
    simpa only [rationalPoints.map_apply, Grp.id_hom_hom, Category.comp_id] using
      h (Subgroup.mem_map_of_mem (rationalPoints.map (𝟙 T.toGrp)) hg)
  have hDSle : DS.neutral.integralPoints ≤ DS.full.integralPoints := by
    rw [← DS.neutralPoints_eq]
    exact DS.neutralPoints_le_full
  calc
    M.integralPoints ≤ DT.neutral.integralPoints := hMneutral
    _ ≤ DS.neutral.integralPoints.map (rationalPoints.map q) :=
      hLift F S T hS htorusT q hq hker DS DT hDSpts hDTpts
    _ ≤ DS.full.integralPoints.map (rationalPoints.map q) := Subgroup.map_mono hDSle
    _ = (characterValuationKernel (fixedFieldValuation F) S.toGrp).map
        (rationalPoints.map q) := by rw [hDSpts]
    _ ≤ torusNormIwahori (inertiaFixedField F) L (intermediateValuation F L) T := hNorm
set_option maxHeartbeats 1500000 in
/-- Choose the norm presentation, then apply the supplied-presentation bound. -/
theorem unramifiedTorusConnectedBoundAssembly :
    UnramifiedTorusConnectedBoundAssemblyStatement.{u} := by
  intro hBdd hLift hNorm F _ _ _ _ T _ L _ _ hT M hM hMgc
  obtain ⟨S, hSAff, hS, q, hq, hker, hNormq⟩ := hNorm F T L hT
  exact connectedBound_of_neutral_lifting_and_norm_presentation
    hBdd hLift F T L hT S hS q hq hker hNormq M hM hMgc

end Langlands.BruhatTits.IntegralModels
