import Langlands.GroupScheme.Reductive.EtaleRankOneNeighbourhood
import Langlands.GroupScheme.Torus.IdentityTransporterEtaleLift

/-! # Actual rank-one neighbourhoods from a geometric Weyl transporter -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.splitTorus

variable {r : Type u} [CommRing r] (I : Type u) [Fintype I] [DecidableEq I]
  (G : GroupScheme (Spec (CommRingCat.of r))) [Smooth G.X.hom] [IsAffineHom G.X.hom]
  (i : splitTorus (Spec (CommRingCat.of r)) I ⟶ G)

local instance geometricRankOne_smooth_geometricFiber (s : Spec (CommRingCat.of r)) :
    Smooth (geometricFiber G s).X.hom :=
  inferInstanceAs (Smooth (CategoryTheory.Limits.pullback.snd G.X.hom (geometricPoint _ s)))

local instance geometricRankOne_affine_geometricFiber (s : Spec (CommRingCat.of r)) :
    IsAffineHom (geometricFiber G s).X.hom :=
  inferInstanceAs (IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (geometricPoint _ s)))

/-- Actual original geometric rank-one data and a geometric identity-component
transporter construct a good neighbourhood, with no local-section premise. -/
def rankOneIdentityComponentReductiveNeighbourhood_of_geometricTransporter
    (hi : IsClosedSubgroup i) (s : Spec (CommRingCat.of r))
    (hself : s ∈ geometricSelfCentralizingTorusLocus I G i)
    (m : I → ℤ) (hm : m ≠ 0)
    (hroots : ∀ a : I → ℤ,
      a ∈ geometricExponentRoots I G i s ↔ a = m ∨ a = -m)
    (hpos : exponentWeightRank I G i m s = 1)
    (hneg : exponentWeightRank I G i (-m) s = 1)
    (e : (I → ℤ) ≃ₗ[ℤ] (I → ℤ)) (he : e m = -m)
    (g₀ : Over.mk (𝟙 (Spec (CommRingCat.of
        (AlgebraicClosure ((Spec (CommRingCat.of r)).residueField s)))) ) ⟶
      (identityComponent (geometricFiber G s)).X)
    (htrans : PointwiseSchemeAction.IsTransporter
      ((exponentIso _ I e).hom ≫ geometricIdentityComponentHom I G i s)
      (geometricIdentityComponentHom I G i s) g₀) :
    IdentityComponentReductiveOpenNeighbourhood G s := by
  let q := geometricPoint (Spec (CommRingCat.of r)) s
  let gk := g₀ ≫ (identityComponentι (geometricFiber G s)).hom.hom
  have hcanon : PointwiseSchemeAction.IsTransporter
      ((exponentIso _ I e).hom ≫ geometricFiberHom I G i s)
      (geometricFiberHom I G i s) gk := by
    simpa only [Category.assoc, geometricIdentityComponentHom_comp] using
      htrans.map (identityComponentι (geometricFiber G s))
  have hcoord : (baseChangeIso q I).hom ≫
      ((exponentIso _ I e).hom ≫ (baseChangeIso q I).inv ≫ (baseChange q).map i) =
        (baseChange q).map (exponentIso (Spec (CommRingCat.of r)) I e).hom ≫
          (baseChange q).map i := by
    rw [← Category.assoc, exponentIso_baseChange, Category.assoc,
      Iso.hom_inv_id_assoc]
  have hraw : PointwiseSchemeAction.IsTransporter
      ((baseChange q).map ((exponentIso (Spec (CommRingCat.of r)) I e).hom ≫ i))
      ((baseChange q).map i) gk := by
    have h := hcanon.precomp (baseChangeIso q I).hom
    change PointwiseSchemeAction.IsTransporter
      ((baseChangeIso q I).hom ≫
        ((exponentIso _ I e).hom ≫ (baseChangeIso q I).inv ≫ (baseChange q).map i))
      ((baseChangeIso q I).hom ≫ (baseChangeIso q I).inv ≫ (baseChange q).map i) gk at h
    rwa [hcoord, Iso.hom_inv_id_assoc, ← Functor.map_comp] at h
  have hidentity : Set.range gk.left ⊆ IdentityComponent.identitySet (geometricFiber G s) := by
    rintro _ ⟨x, rfl⟩
    change (identityComponentι (geometricFiber G s)).hom.hom.left (g₀.left x) ∈ _
    have hx : (identityComponentι (geometricFiber G s)).hom.hom.left (g₀.left x) ∈
        Set.range (identityComponentι (geometricFiber G s)).hom.hom.left := ⟨g₀.left x, rfl⟩
    exact (IdentityComponent.range_identityComponentι (geometricFiber G s)).le hx
  have hqs : q default = s := by
    change (Spec (CommRingCat.of r)).fromSpecResidueField s _ = s
    exact Scheme.fromSpecResidueField_apply _ _
  let d := PointwiseSchemeAction.etaleIdentityTransporterOfSplitTorus
    ((exponentIso (Spec (CommRingCat.of r)) I e).hom ≫ i) i
    (inferInstance : Smooth G.X.hom) s q hqs gk hraw hidentity
  let t := Classical.choose d.mem_range
  have hdt : d.projection t = s := Classical.choose_spec d.mem_range
  let H := (baseChange d.projection).obj G
  let : Smooth H.X.hom :=
    inferInstanceAs (Smooth (CategoryTheory.Limits.pullback.snd G.X.hom d.projection))
  let : IsAffineHom H.X.hom :=
    MorphismProperty.pullback_snd G.X.hom d.projection inferInstance
  let g := d.baseChangedSection.left
  have hg : g ≫ H.X.hom = 𝟙 _ := Over.w d.baseChangedSection
  have hin := d.baseChangedSection_inIdentity
  have hrange : Set.range g ⊆ RelativeIdentityComponent.underlyingSet H :=
    (RelativeIdentityComponent.inRelativeIdentityComponent_iff_range_subset H
      d.baseChangedSection).mp hin
  have hres : Langlands.AlgebraicGeometry.SectionComponent.fiberPoint H.X.hom g hg t ∈
      IdentityComponent.identitySet (RelativeIdentityComponent.residueFiber H t) :=
    (RelativeIdentityComponent.mem_sectionIdentityOpen_iff H g hg t).mp
      (hrange ⟨t, rfl⟩)
  let dn := RelativeIdentityComponent.sectionIdentityNeighbourhood H g hg t hres
  have htrans' := isTransporter_baseChange_coordinates I i d.projection e
    d.baseChangedSection d.baseChangedSection_isTransporter
  exact rankOneIdentityComponentReductiveNeighbourhood_of_affineEtale I G i d.projection
    hi s hself m hm hroots hpos hneg e he d.etale t hdt hg dn htrans'

end Langlands.GroupScheme.splitTorus
