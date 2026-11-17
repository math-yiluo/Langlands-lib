import Langlands.GroupScheme.Reductive.ConnectedFibreLocusDvrCore
import Langlands.GroupScheme.Reductive.ConnectedFibreDvrGeometry

/-! # Connectedness specializes for smooth affine groups over DVRs -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme.ConnectedFibreLocus

/-- Connectedness of the generic fibre specializes to the special fibre when
every geometric fibre identity component is reductive. -/
theorem dvrCore : DvrCoreStatement.{u} := by
  intro R K _ _ _ _ _ _ G _ _ hG hconn
  obtain ⟨H, i, hi, hsm, hgc⟩ :=
    RelativeIdentityComponent.smoothExistence _ G inferInstance
  let : Smooth H.X.hom := hsm
  let : GeometricallyConnected H.X.hom := hgc
  let : IsOpenImmersion i.hom.hom.left := hi.isOpenImmersion
  let : IsAffineHom H.X.hom :=
    RelativeIdentityComponent.smoothDvrAffineness R G inferInstance inferInstance H i hi
  have hH : IsReductive H :=
    ConnectedFibreClosedGeometry.isReductive_relativeIdentityComponent i hi hG
  let b := algebraBaseMap R K
  let HK := (baseChange b).obj H
  let GK := (baseChange b).obj G
  let j : HK ⟶ GK := (baseChange b).map i
  let : Smooth HK.X.hom :=
    inferInstanceAs (Smooth (pullback.snd H.X.hom b))
  let : IsAffineHom HK.X.hom :=
    inferInstanceAs (IsAffineHom (pullback.snd H.X.hom b))
  let : Smooth GK.X.hom :=
    inferInstanceAs (Smooth (pullback.snd G.X.hom b))
  let : IsAffineHom GK.X.hom :=
    inferInstanceAs (IsAffineHom (pullback.snd G.X.hom b))
  let : ConnectedSpace HK.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton (pullback.snd H.X.hom b)
  let : ConnectedSpace GK.X.left := hconn
  let : IsOpenImmersion j.hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @IsOpenImmersion) b i.hom.hom inferInstance
  let : IsClosedImmersion j.hom.hom.left := HomImage.isClosedSubgroup_of_mono j
  have hrange : Set.range j.hom.hom.left = Set.univ :=
    (show IsClopen (Set.range j.hom.hom.left) from
      ⟨j.hom.hom.left.isClosedEmbedding.isClosed_range,
        IsOpenImmersion.isOpen_range _⟩).eq_univ (Set.range_nonempty _)
  let : Epi j.hom.hom.left.base :=
    (TopCat.epi_iff_surjective _).mpr (Set.range_eq_univ.mp hrange)
  let : IsIso j.hom.hom.left := IsOpenImmersion.isIso _
  let : IsIso ((baseChange (algebraBaseMap R K)).map i) :=
    TorusIsomorphismLocus.isIso_of_underlying j
  let : IsIso i := EtaleOpenGenericIsomorphism.isIso_of_dvr (K := K) hH i
  let c := algebraBaseMap R (IsLocalRing.ResidueField R)
  let ik := (baseChange c).map i
  let : IsIso ik.hom.hom.left :=
    Functor.map_isIso (Grp.forget₂Mon _ ⋙ Mon.forget _ ⋙ Over.forget _) ik
  let : ConnectedSpace ((baseChange c).obj H).X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton (pullback.snd H.X.hom c)
  exact ik.hom.hom.left.homeomorph.surjective.connectedSpace
    ik.hom.hom.left.continuous

end Langlands.GroupScheme.ConnectedFibreLocus
