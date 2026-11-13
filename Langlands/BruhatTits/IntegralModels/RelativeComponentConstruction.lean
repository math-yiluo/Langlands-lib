import Langlands.BruhatTits.IntegralModels.RelativeComponent
import Langlands.GroupScheme.RelativeIdentityComponent.SmoothExistenceProof
import Langlands.GroupScheme.RelativeIdentityComponent.SmoothBaseChangeProof
import Langlands.GroupScheme.RelativeIdentityComponentDvrAffinenessProof

/-! # Relative-component model data from a smooth affine integral model -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- A group scheme with geometrically connected fibres represents its own
relative identity component, on every test scheme. -/
theorem isRelativeIdentityComponent_id_of_geometricallyConnected
    {S : Scheme.{u}} (H : GroupScheme S) [GeometricallyConnected H.X.hom] :
    IsRelativeIdentityComponent H (𝟙 H) := by
  refine ⟨?_, fun T x => ?_⟩
  · change IsOpenImmersion (𝟙 H.X.left)
    infer_instance
  · constructor
    · intro _ s
      let : ConnectedSpace (RelativeIdentityComponent.residueFiber H s).X.left :=
        inferInstanceAs (ConnectedSpace (H.X.hom.fiber s))
      change Set.range (RelativeIdentityComponent.residueFiberPoint H x s).left ⊆
        connectedComponent _
      rw [PreconnectedSpace.connectedComponent_eq_univ]
      exact Set.subset_univ _
    · intro _
      exact ⟨x, Category.comp_id x⟩

namespace IntegralModel

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  {G : GroupScheme (Spec (CommRingCat.of K))}

omit [IsDiscreteValuationRing R] in
/-- A supplied generic isomorphism transports geometric connectedness to the
actual generic fibre before that identification is applied. -/
theorem genericFibre_geometricallyConnected (M : IntegralModel R K G)
    (hG : GeometricallyConnected G.X.hom) :
    GeometricallyConnected M.genericFibre.X.hom := by
  let e : M.genericFibre.X ≅ G.X := (Grp.forget _).mapIso M.genericIso
  have : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
  have hp : CategoryTheory.IsPullback e.hom.left M.genericFibre.X.hom G.X.hom (𝟙 _) :=
    CategoryTheory.IsPullback.of_horiz_isIso ⟨by
      rw [Category.comp_id]
      exact e.hom.w⟩
  exact MorphismProperty.of_isPullback hp hG

/-- Any smooth affine integral model of a geometrically connected generic group
over a DVR admits actual affine relative-component model data with the original
full model and its original generic identification. -/
def relativeComponentModelDataOfSmooth (M : IntegralModel R K G) (hM : M.IsSmooth)
    (hG : GeometricallyConnected G.X.hom) :
    Langlands.BruhatTits.IntegralModels.RelativeComponentModelData R K G := by
  let hex := RelativeIdentityComponent.smoothExistence _ M.group hM
  let H := Classical.choose hex
  let i := Classical.choose (Classical.choose_spec hex)
  have hs := Classical.choose_spec (Classical.choose_spec hex)
  have hi := hs.1
  have hH := hs.2.1
  have hconn := hs.2.2
  let : Smooth H.X.hom := hH
  let : GeometricallyConnected H.X.hom := hconn
  let : IsAffineHom H.X.hom :=
    RelativeIdentityComponent.smoothDvrAffineness R M.group hM M.affine H i hi
  let : GeometricallyConnected M.genericFibre.X.hom :=
    M.genericFibre_geometricallyConnected hG
  have hiK := RelativeIdentityComponent.smoothBaseChange _ M.group hM H i hi
    _ (Spec.algebraMap R K)
  let e := hiK.iso (isRelativeIdentityComponent_id_of_geometricallyConnected
    M.genericFibre)
  have he : e.hom = (GroupScheme.baseChange (Spec.algebraMap R K)).map i := by
    simpa only [Category.comp_id] using hiK.iso_hom_comp
      (isRelativeIdentityComponent_id_of_geometricallyConnected M.genericFibre)
  let N : IntegralModel R K G := {
    group := H
    affine := inferInstance
    flat := inferInstance
    finiteType := inferInstance
    genericIso := e ≪≫ M.genericIso }
  exact {
    full := M
    neutral := N
    full_smooth := hM
    neutral_smooth := hH
    neutral_connectedFibres := N.hasConnectedFibres_of_geometricallyConnected hconn
    inclusion := {
      hom := i
      generic_comm := by
        change _ ≫ M.genericIso.hom = (e.hom ≫ M.genericIso.hom) ≫ 𝟙 G
        rw [he, Category.comp_id] }
    isRelativeComponent := hi }

/-- Taking the neutral model preserves the full model literally. -/
@[simp] theorem relativeComponentModelDataOfSmooth_full (M : IntegralModel R K G)
    (hM : M.IsSmooth) (hG : GeometricallyConnected G.X.hom) :
    (M.relativeComponentModelDataOfSmooth hM hG).full = M := by
  unfold relativeComponentModelDataOfSmooth
  rfl

end IntegralModel
end Langlands.GroupScheme
