import Langlands.GroupScheme.RelativeIdentityComponent.UnderlyingSet
import Langlands.GroupScheme.RelativeIdentityComponentProperties

/-! # Arbitrary base change of relative identity-component representatives -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace RelativeIdentityComponent

/-- The square underlying pullback of a morphism in an over category. -/
theorem overPullback_isPullback {S S' : Scheme.{u}} (b : S' ⟶ S)
    {X Y : Over S} (f : X ⟶ Y) :
    IsPullback ((Over.pullback b).map f).left (pullback.fst X.hom b)
      (pullback.fst Y.hom b) f.left := by
  have houter : IsPullback
      (((Over.pullback b).map f).left ≫ pullback.snd Y.hom b)
      (pullback.fst X.hom b) b (f.left ≫ Y.hom) := by
    simpa only [Over.w f, Over.pullback_map_left, pullback.lift_snd] using
      (IsPullback.of_hasPullback X.hom b).flip
  exact houter.of_right
    (show ((Over.pullback b).map f).left ≫ pullback.fst Y.hom b =
        pullback.fst X.hom b ≫ f.left by
      simp only [Over.pullback_map_left, pullback.lift_fst])
    (IsPullback.of_hasPullback Y.hom b).flip

/-- Images in a scheme pullback are inverse images of the original images. -/
theorem range_of_isPullback {P X Y Z : Scheme.{u}} {a : P ⟶ X} {b : P ⟶ Y}
    {c : X ⟶ Z} {d : Y ⟶ Z} (h : IsPullback a b c d) :
    Set.range a = c ⁻¹' Set.range d := by
  simpa using Scheme.image_preimage_eq_of_isPullback h.flip Set.univ

/-- The comparison from a fibre after base change to the original residue fibre. -/
def fiberComparison {S S' : Scheme.{u}} (b : S' ⟶ S) (X : Over S) (s' : S') :
    ((Over.pullback b).obj X).hom.fiber s' ⟶ X.hom.fiber (b s') :=
  pullback.map _ _ _ _ (pullback.fst X.hom b) (Spec.map (b.residueFieldMap s')) b
    pullback.condition.symm (by simp)

/-- The fibre comparison is itself a base change along the residue-field map. -/
theorem fiberComparison_isPullback {S S' : Scheme.{u}} (b : S' ⟶ S)
    (X : Over S) (s' : S') :
    IsPullback (fiberComparison b X s')
      (((Over.pullback b).obj X).hom.fiberToSpecResidueField s')
      (X.hom.fiberToSpecResidueField (b s')) (Spec.map (b.residueFieldMap s')) :=
  isPullback_fiberToSpecResidueField_of_isPullback
    (IsPullback.of_hasPullback X.hom b) s'

/-- The fibre comparisons commute with every map over the base. -/
@[reassoc]
theorem fiberComparison_naturality {S S' : Scheme.{u}} (b : S' ⟶ S)
    {X Y : Over S} (f : X ⟶ Y) (s' : S') :
    (((Over.pullback (S'.fromSpecResidueField s')).map ((Over.pullback b).map f)).left) ≫
        fiberComparison b Y s' =
      fiberComparison b X s' ≫
        (((Over.pullback (S.fromSpecResidueField (b s'))).map f).left) := by
  apply pullback.hom_ext <;>
    simp [fiberComparison, Over.pullback_map_left]

/-- The square comparing the fibre maps before and after base change is cartesian. -/
theorem fiberMap_isPullback {S S' : Scheme.{u}} (b : S' ⟶ S)
    {X Y : Over S} (f : X ⟶ Y) (s' : S') :
    IsPullback
      (((Over.pullback (S'.fromSpecResidueField s')).map ((Over.pullback b).map f)).left)
      (fiberComparison b X s') (fiberComparison b Y s')
      (((Over.pullback (S.fromSpecResidueField (b s'))).map f).left) := by
  have houter : IsPullback (fiberComparison b X s')
      ((((Over.pullback (S'.fromSpecResidueField s')).map ((Over.pullback b).map f)).left) ≫
        ((Over.pullback (S'.fromSpecResidueField s')).obj ((Over.pullback b).obj Y)).hom)
      ((((Over.pullback (S.fromSpecResidueField (b s'))).map f).left) ≫
        ((Over.pullback (S.fromSpecResidueField (b s'))).obj Y).hom)
      (Spec.map (b.residueFieldMap s')) := by
    simpa only [Over.pullback_obj_hom, Over.pullback_map_left, pullback.lift_snd,
      Scheme.Hom.fiberToSpecResidueField] using fiberComparison_isPullback b X s'
  exact (houter.of_bot (fiberComparison_naturality b f s').symm
    (fiberComparison_isPullback b Y s')).flip

end RelativeIdentityComponent

namespace IsRelativeIdentityComponent

variable {S : Scheme.{u}} {G H : GroupScheme S} {i : H ⟶ G}

/-- The image of a supplied representative is exactly the relative identity set. -/
theorem range_eq_underlyingSet (hi : IsRelativeIdentityComponent G i) :
    Set.range i.hom.hom.left = RelativeIdentityComponent.underlyingSet G := by
  apply Set.Subset.antisymm
  · exact (RelativeIdentityComponent.factors_iff_range_subset G hi H.X i.hom.hom).mp
      ⟨𝟙 _, Category.id_comp _⟩
  · intro z hz
    let T : Over S := Over.mk (G.X.left.fromSpecResidueField z ≫ G.X.hom)
    let x : T ⟶ G.X := Over.homMk (G.X.left.fromSpecResidueField z)
    have hx : Set.range x.left ⊆ RelativeIdentityComponent.underlyingSet G := by
      change Set.range (G.X.left.fromSpecResidueField z) ⊆ _
      rw [Scheme.range_fromSpecResidueField]
      exact Set.singleton_subset_iff.mpr hz
    obtain ⟨y, hy⟩ :=
      (RelativeIdentityComponent.factors_iff_range_subset G hi T x).mpr hx
    refine ⟨y.left (IsLocalRing.closedPoint (G.X.left.residueField z)), ?_⟩
    have he := congrArg
      (fun f : T ⟶ G.X => f.left (IsLocalRing.closedPoint (G.X.left.residueField z))) hy
    change i.hom.hom.left (y.left _) = (G.X.left.fromSpecResidueField z) _ at he
    simpa only [Scheme.fromSpecResidueField_apply] using he

/-- On every residue fibre, the inclusion has image the entire identity component. -/
theorem range_residueFiber (hi : IsRelativeIdentityComponent G i) (s : S) :
    Set.range (((GroupScheme.baseChange (S.fromSpecResidueField s)).map i).hom.hom.left) =
      IdentityComponent.identitySet (RelativeIdentityComponent.residueFiber G s) := by
  have hr := RelativeIdentityComponent.range_of_isPullback
    (RelativeIdentityComponent.overPullback_isPullback (S.fromSpecResidueField s) i.hom.hom)
  change Set.range
    (((Over.pullback (S.fromSpecResidueField s)).map i.hom.hom).left) = _ at hr ⊢
  rw [hr, hi.range_eq_underlyingSet]
  ext y
  exact RelativeIdentityComponent.fiberι_mem_underlyingSet_iff G s y

/-- A representative inclusion is closed on each residue fibre. -/
theorem isClosedImmersion_residueFiber (hi : IsRelativeIdentityComponent G i) (s : S) :
    IsClosedImmersion
      (((GroupScheme.baseChange (S.fromSpecResidueField s)).map i).hom.hom.left) := by
  let : IsOpenImmersion i.hom.hom.left := hi.isOpenImmersion
  have : IsOpenImmersion
      (((GroupScheme.baseChange (S.fromSpecResidueField s)).map i).hom.hom.left) :=
    MorphismProperty.of_isPullback
      (RelativeIdentityComponent.overPullback_isPullback (S.fromSpecResidueField s) i.hom.hom).flip
      hi.isOpenImmersion
  exact IsClosedImmersion.of_isPreimmersion _ (by
    rw [hi.range_residueFiber]
    exact isClosed_connectedComponent)

/-- Exact fibre images determine the image of the inclusion in the total space. -/
theorem range_eq_underlyingSet_of_residueFiber
    (hr : ∀ s : S,
      Set.range (((GroupScheme.baseChange (S.fromSpecResidueField s)).map i).hom.hom.left) =
        IdentityComponent.identitySet (RelativeIdentityComponent.residueFiber G s)) :
    Set.range i.hom.hom.left = RelativeIdentityComponent.underlyingSet G := by
  have hpre (s : S) :
      G.X.hom.fiberι s ⁻¹' Set.range i.hom.hom.left =
        IdentityComponent.identitySet (RelativeIdentityComponent.residueFiber G s) :=
    (RelativeIdentityComponent.range_of_isPullback
      (RelativeIdentityComponent.overPullback_isPullback (S.fromSpecResidueField s)
        i.hom.hom)).symm.trans (hr s)
  apply Set.Subset.antisymm
  · intro z hz
    refine ⟨G.X.hom z, G.X.hom.asFiber z, ?_, G.X.hom.fiberι_asFiber z⟩
    rw [← hpre]
    simpa only [Set.mem_preimage, Scheme.Hom.fiberι_asFiber] using hz
  · rintro _ ⟨s, y, hy, rfl⟩
    change y ∈ G.X.hom.fiberι s ⁻¹' Set.range i.hom.hom.left
    rw [hpre]
    exact hy

/-- An open subgroup with the exact total-space image represents the all-test condition. -/
theorem of_range_eq_underlyingSet [IsOpenImmersion i.hom.hom.left]
    (hr : Set.range i.hom.hom.left = RelativeIdentityComponent.underlyingSet G) :
    IsRelativeIdentityComponent G i := by
  refine ⟨inferInstance, fun T x => ?_⟩
  rw [RelativeIdentityComponent.inRelativeIdentityComponent_iff_range_subset, ← hr]
  constructor
  · rintro ⟨y, rfl⟩
    rintro _ ⟨t, rfl⟩
    exact ⟨y.left t, rfl⟩
  · intro hx
    exact ⟨FiniteEtaleImage.liftOver i.hom.hom x hx,
      FiniteEtaleImage.liftOver_fac i.hom.hom x hx⟩

/-- An open subgroup with exact identity-component images in the fibres represents them. -/
theorem of_range_residueFiber [IsOpenImmersion i.hom.hom.left]
    (hr : ∀ s : S,
      Set.range (((GroupScheme.baseChange (S.fromSpecResidueField s)).map i).hom.hom.left) =
        IdentityComponent.identitySet (RelativeIdentityComponent.residueFiber G s)) :
    IsRelativeIdentityComponent G i :=
  of_range_eq_underlyingSet (range_eq_underlyingSet_of_residueFiber hr)

/-- A geometrically connected representative remains a representative after any base change. -/
theorem baseChange (hi : IsRelativeIdentityComponent G i)
    [GeometricallyConnected H.X.hom] {S' : Scheme.{u}} (b : S' ⟶ S) :
    IsRelativeIdentityComponent ((GroupScheme.baseChange b).obj G)
      ((GroupScheme.baseChange b).map i) := by
  let : IsOpenImmersion i.hom.hom.left := hi.isOpenImmersion
  let j := (GroupScheme.baseChange b).map i
  let : IsOpenImmersion j.hom.hom.left :=
    MorphismProperty.of_isPullback
      (RelativeIdentityComponent.overPullback_isPullback b i.hom.hom).flip hi.isOpenImmersion
  apply of_range_residueFiber
  intro s'
  let c := S'.fromSpecResidueField s'
  let j' := (GroupScheme.baseChange c).map j
  let : IsOpenImmersion j'.hom.hom.left :=
    MorphismProperty.of_isPullback
      (RelativeIdentityComponent.overPullback_isPullback c j.hom.hom).flip inferInstance
  let : IsClosedImmersion j'.hom.hom.left :=
    MorphismProperty.of_isPullback
      (RelativeIdentityComponent.fiberMap_isPullback b i.hom.hom s').flip
      (hi.isClosedImmersion_residueFiber (b s'))
  let : GeometricallyConnected ((GroupScheme.baseChange b).obj H).X.hom :=
    inferInstanceAs (GeometricallyConnected (pullback.snd H.X.hom b))
  let : ConnectedSpace ((GroupScheme.baseChange c).obj
      ((GroupScheme.baseChange b).obj H)).X.left :=
    inferInstanceAs (ConnectedSpace (((GroupScheme.baseChange b).obj H).X.hom.fiber s'))
  exact IdentityComponent.range_eq_identitySet
    ((GroupScheme.baseChange c).obj ((GroupScheme.baseChange b).obj G)) j'

end IsRelativeIdentityComponent

namespace RelativeIdentityComponent

/-- Smooth existence implies unrestricted base-change compatibility. -/
theorem smoothBaseChange_of_existence (hex : SmoothExistenceStatement.{u}) :
    SmoothBaseChangeStatement.{u} := by
  intro S G hG H i hi S' b
  obtain ⟨H', j, hj, -, hconn⟩ := hex S G hG
  let : GeometricallyConnected H'.X.hom := hconn
  let : GeometricallyConnected H.X.hom := hi.geometricallyConnected hj
  exact hi.baseChange b

/-- Smooth existence supplies all three assertions of the smooth structure target. -/
theorem smoothStructure_of_existence (hex : SmoothExistenceStatement.{u}) :
    SmoothStructureStatement.{u} :=
  ⟨hex, smoothNormality_of_existence hex, smoothBaseChange_of_existence hex⟩

end RelativeIdentityComponent
end Langlands.GroupScheme
