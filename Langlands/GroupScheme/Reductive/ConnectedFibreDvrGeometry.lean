import Langlands.GroupScheme.Reductive.SmoothTargetGenericClosure
import Langlands.GroupScheme.Reductive.EtaleDvrOpenIsomorphism
import Langlands.GroupScheme.Reductive.IdentityComponentLocusBaseChange
import Langlands.GroupScheme.RelativeIdentityComponentDvrAffinenessProof
import Langlands.GroupScheme.RelativeIdentityComponent.SmoothExistenceProof
import Langlands.GroupScheme.RelativeIdentityComponent.BaseChange

/-! # Closed relative identity components over discrete valuation rings -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme.ConnectedFibreClosedGeometry

/-- A reductive monomorphism into a smooth affine group over a DVR is closed. -/
theorem isClosedImmersion_of_reductive_dvr
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {M G : GroupScheme (Spec (CommRingCat.of R))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (hM : IsReductive M) (f : M ⟶ G) [Mono f.hom.hom.left] :
    IsClosedImmersion f.hom.hom.left := by
  let K := FractionRing R
  let : Smooth M.X.hom := hM.smooth
  let : IsAffineHom M.X.hom := hM.isAffineHom
  let : Smooth (ReductiveGenericClosure.closure (K := K) f).X.hom :=
    ReductiveGenericClosure.closure_smooth f hM
  let : IsOpenImmersion (ReductiveGenericClosure.factor (K := K) f).hom.hom.left :=
    ReductiveGenericClosure.factor_isOpenImmersion f hM
  have hgeneric :
      IsIso ((baseChange (algebraBaseMap R K)).map
        (ReductiveGenericClosure.factor (K := K) f)) := by
    change IsIso ((baseChange (Spec.algebraMap R K)).map
      (GenericSubgroupClosure.factor G _ f (𝟙 _) (by simp)))
    rw [GenericSubgroupClosure.baseChange_factor, Category.id_comp]
    infer_instance
  let := hgeneric
  let := EtaleOpenGenericIsomorphism.isIso_of_dvr (K := K) hM
    (ReductiveGenericClosure.factor (K := K) f)
  rw [← ReductiveGenericClosure.factor_inclusion (K := K) f]
  change IsClosedImmersion
    ((ReductiveGenericClosure.factor (K := K) f).hom.hom.left ≫
      (ReductiveGenericClosure.inclusion (K := K) f).hom.hom.left)
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
  infer_instance

/-- An affine smooth representative of the relative identity component is
reductive when every geometric identity component of the ambient group is. -/
theorem isReductive_relativeIdentityComponent
    {S : Scheme.{u}} {G H : GroupScheme S}
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    [Smooth H.X.hom] [IsAffineHom H.X.hom] [GeometricallyConnected H.X.hom]
    (i : H ⟶ G) (hi : IsRelativeIdentityComponent G i)
    (hG : identityComponentReductiveLocus G = Set.univ) :
    IsReductive H := by
  refine ⟨inferInstance, inferInstance, fun s => ?_⟩
  let b := geometricPoint S s
  let j := (baseChange b).map i
  let : Smooth (geometricFiber G s).X.hom :=
    inferInstanceAs (Smooth (pullback.snd G.X.hom b))
  let : IsAffineHom (geometricFiber G s).X.hom :=
    inferInstanceAs (IsAffineHom (pullback.snd G.X.hom b))
  let : Smooth (geometricFiber H s).X.hom :=
    inferInstanceAs (Smooth (pullback.snd H.X.hom b))
  let : IsAffineHom (geometricFiber H s).X.hom :=
    inferInstanceAs (IsAffineHom (pullback.snd H.X.hom b))
  let : ConnectedSpace (geometricFiber H s).X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton
      (pullback.snd H.X.hom b)
  let : IsOpenImmersion i.hom.hom.left := hi.isOpenImmersion
  let : IsOpenImmersion j.hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @IsOpenImmersion) b i.hom.hom inferInstance
  let : IsClosedImmersion j.hom.hom.left := HomImage.isClosedSubgroup_of_mono j
  have hred : IsConnectedReductive (identityComponent (geometricFiber G s)) := by
    have : s ∈ identityComponentReductiveLocus G := by rw [hG]; trivial
    exact this
  exact (hred.of_iso (IdentityComponent.isoOfIsOpenImmersion _ j)).isPseudoReductive

/-- Every smooth geometrically connected relative identity component is closed
over a DVR when the ambient geometric identity components are reductive. -/
theorem isClosedImmersion_relativeIdentityComponent_dvr
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {G H : GroupScheme (Spec (CommRingCat.of R))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    [Smooth H.X.hom] [GeometricallyConnected H.X.hom]
    (i : H ⟶ G) (hi : IsRelativeIdentityComponent G i)
    (hG : identityComponentReductiveLocus G = Set.univ) :
    IsClosedImmersion i.hom.hom.left := by
  let : IsOpenImmersion i.hom.hom.left := hi.isOpenImmersion
  let : IsAffineHom H.X.hom :=
    RelativeIdentityComponent.smoothDvrAffineness R G inferInstance inferInstance H i hi
  exact isClosedImmersion_of_reductive_dvr
    (isReductive_relativeIdentityComponent i hi hG) i

end Langlands.GroupScheme.ConnectedFibreClosedGeometry
