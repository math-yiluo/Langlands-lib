import Langlands.GroupScheme.Reductive.GaloisPinningIso
import Langlands.GroupScheme.Reductive.TorusTransportPinning
import Langlands.GroupScheme.Dynamic.CentralizerReductiveTransport
import Langlands.GroupScheme.Reductive.RootPinningFromSplitTorus
import Langlands.GroupScheme.Torus.StrictHenselianMaximalReduction

/-! # Transport of Galois pinning data along an isomorphism of groups -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.GaloisPinningData

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {G G' : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] [IsAffineHom G'.X.hom]

local instance galoisPinningTransportAffine {H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom H.X.hom] :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k K)).obj H).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd H.X.hom (algebraBaseMap k K))
  infer_instance

variable (d : GaloisPinningData k K G) (e : G ≅ G')

omit [IsAffineHom G'.X.hom] in
include d e in
theorem transport_isConnectedReductive :
    IsConnectedReductive ((GroupScheme.baseChange (algebraBaseMap k K)).obj G') :=
  IsConnectedReductive.of_iso ((GroupScheme.baseChange (algebraBaseMap k K)).mapIso e).symm
    d.isConnectedReductive

omit [IsAffineHom G'.X.hom] in
theorem transport_isMaximalTorus :
    IsMaximalTorus (T := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj d.torus)
      ((GroupScheme.baseChange (algebraBaseMap k K)).map (d.inclusion ≫ e.hom)) :=
  IsMaximalTorus.of_eq_iso_comp_comp_iso d.isMaximalTorus (Iso.refl _)
    ((GroupScheme.baseChange (algebraBaseMap k K)).mapIso e)
    (by rw [Functor.map_comp, Iso.refl_hom, Category.id_comp]; rfl)

/-- The identity of the split torus over `K`, as the base change of the identity over `k`. -/
abbrev transportTorusIso :
    (CommGroupScheme.baseChange (algebraBaseMap k K)).obj d.torus ≅
      (CommGroupScheme.baseChange (algebraBaseMap k K)).obj d.torus :=
  (CommGroupScheme.baseChange (algebraBaseMap k K)).mapIso (Iso.refl d.torus)

theorem groupHom_refl (T : CommGroupScheme (Spec (CommRingCat.of k))) :
    CommGroupScheme.groupHom (Iso.refl T).hom = 𝟙 T.toGrp :=
  rfl

omit [IsAffineHom G'.X.hom] in
theorem transport_square :
    (GroupScheme.baseChange (algebraBaseMap k K)).map d.inclusion ≫
        ((GroupScheme.baseChange (algebraBaseMap k K)).mapIso e).hom =
      CommGroupScheme.groupHom (d.transportTorusIso (K := K)).hom ≫
        (GroupScheme.baseChange (algebraBaseMap k K)).map (d.inclusion ≫ e.hom) := by
  change (GroupScheme.baseChange (algebraBaseMap k K)).map d.inclusion ≫
      (GroupScheme.baseChange (algebraBaseMap k K)).map e.hom =
    (GroupScheme.baseChange (algebraBaseMap k K)).map
        (CommGroupScheme.groupHom (Iso.refl d.torus).hom) ≫
      (GroupScheme.baseChange (algebraBaseMap k K)).map (d.inclusion ≫ e.hom)
  rw [groupHom_refl, ← Functor.map_comp, ← Functor.map_comp, Category.id_comp]

/-- **Transport of Galois pinning data along an isomorphism `e : G ≅ G'` over `k`.** The torus
is that of `d`, with inclusion `d.inclusion ≫ e.hom`; the root datum and base are those of `d`
(transported along the identity of `T_K`), with the same root indices. The simple-root Lie
vectors are chosen by the Library's root-line theorem. -/
def transport : GaloisPinningData k K G' where
  torus := d.torus
  inclusion := d.inclusion ≫ e.hom
  isConnectedReductive := d.transport_isConnectedReductive e
  isSplitTorus := d.isSplitTorus
  isMaximalTorus := d.transport_isMaximalTorus e
  rootIndex := d.rootIndex
  rootDatum := torusTransportRootDatum d.transportTorusIso d.rootDatum
  isRootDatum := d.isRootDatum.torusTransport d.transportTorusIso
    ((GroupScheme.baseChange (algebraBaseMap k K)).mapIso e) (d.transport_square e)
  isReduced := by
    have := d.isReduced
    exact torusTransportRootDatum_isReduced _ _
  base := torusTransportBase d.transportTorusIso d.rootDatum d.base
  pinning := RootPinning.ofSplitMaximalTorus (d.transport_isConnectedReductive e)
    d.isSplitTorus _ (d.transport_isMaximalTorus e)
    (torusTransportRootDatum d.transportTorusIso d.rootDatum)
    (d.isRootDatum.torusTransport d.transportTorusIso
      ((GroupScheme.baseChange (algebraBaseMap k K)).mapIso e) (d.transport_square e))
    (torusTransportBase d.transportTorusIso d.rootDatum d.base)

@[simp] theorem transport_torus : (d.transport e).torus = d.torus :=
  rfl

@[simp] theorem transport_inclusion : (d.transport e).inclusion = d.inclusion ≫ e.hom :=
  rfl

/-- The pinned isomorphism from `d` to its transport along `e`. -/
def transportIso : d.Iso (d.transport e) where
  groupIso := e
  torusIso := Iso.refl d.torus
  square := by
    change d.inclusion ≫ e.hom = CommGroupScheme.groupHom (Iso.refl d.torus).hom ≫
      (d.inclusion ≫ e.hom)
    rw [groupHom_refl, Category.id_comp]
  rootDatumEquiv := torusTransportRootDatumEquiv d.transportTorusIso d.rootDatum
  weightMap_eq _ := rfl
  base_iff a := by
    change a ∈ d.base.support ↔ a ∈ (torusTransportBase d.transportTorusIso d.rootDatum
      d.base).support
    rw [torusTransportBase_support]

@[simp] theorem transportIso_groupIso : (d.transportIso e).groupIso = e :=
  rfl

end Langlands.GroupScheme.GaloisPinningData
