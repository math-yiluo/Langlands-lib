import Langlands.GroupScheme.Reductive.RelativeRankOneNeighbourhood
import Langlands.GroupScheme.Torus.AffineProfileBaseChange

/-! # Descending actual rank-one neighbourhoods from etale bases -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.splitTorus

section TransporterCoordinates

variable {S S' : Scheme.{u}} (I : Type u) [Fintype I] [DecidableEq I]
  {G : GroupScheme S} (i : splitTorus S I ⟶ G) (b : S' ⟶ S)
  (e : (I → ℤ) ≃ₗ[ℤ] (I → ℤ))

/-- A transporter for the actually pulled-back homomorphisms is the same
transporter in canonical standard-torus coordinates over the new base. -/
theorem isTransporter_baseChange_coordinates {V : Over S'}
    (g : V ⟶ ((baseChange b).obj G).X)
    (hg : PointwiseSchemeAction.IsTransporter
      ((baseChange b).map ((exponentIso S I e).hom ≫ i)) ((baseChange b).map i) g) :
    PointwiseSchemeAction.IsTransporter
      ((exponentIso S' I e).hom ≫ (baseChangeIso b I).inv ≫ (baseChange b).map i)
      ((baseChangeIso b I).inv ≫ (baseChange b).map i) g := by
  have hcoord : (baseChangeIso b I).inv ≫ (baseChange b).map (exponentIso S I e).hom =
      (exponentIso S' I e).hom ≫ (baseChangeIso b I).inv := by
    apply (cancel_mono (baseChangeIso b I).hom).mp
    rw [Category.assoc, ← exponentIso_baseChange S I b e]
    simp
  have h := hg.precomp (baseChangeIso b I).inv
  rw [Functor.map_comp, ← Category.assoc, hcoord] at h
  exact h

end TransporterCoordinates

variable {r A : Type u} [CommRing r] [CommRing A]
  (I : Type u) [Fintype I] [DecidableEq I]
  (G : GroupScheme (Spec (CommRingCat.of r))) [Smooth G.X.hom] [IsAffineHom G.X.hom]
  (i : splitTorus (Spec (CommRingCat.of r)) I ⟶ G)
  (b : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of r))

local instance etaleRankOne_smooth_baseChange :
    Smooth ((baseChange b).obj G).X.hom :=
  inferInstanceAs (Smooth (CategoryTheory.Limits.pullback.snd G.X.hom b))

local instance etaleRankOne_affine_baseChange :
    IsAffineHom ((baseChange b).obj G).X.hom :=
  MorphismProperty.pullback_snd G.X.hom b inferInstance

/-- Original-fibre rank-one data and an actual transporter section only after
an affine etale base change construct a good open in the original base. -/
def rankOneIdentityComponentReductiveNeighbourhood_of_affineEtale
    (hi : IsClosedSubgroup i) (s : Spec (CommRingCat.of r))
    (hself : s ∈ geometricSelfCentralizingTorusLocus I G i)
    (m : I → ℤ) (hm : m ≠ 0)
    (hroots : ∀ a : I → ℤ,
      a ∈ geometricExponentRoots I G i s ↔ a = m ∨ a = -m)
    (hpos : exponentWeightRank I G i m s = 1)
    (hneg : exponentWeightRank I G i (-m) s = 1)
    (e : (I → ℤ) ≃ₗ[ℤ] (I → ℤ)) (he : e m = -m)
    (hb : Etale b) (t : Spec (CommRingCat.of A)) (hbt : b t = s)
    {g : Spec (CommRingCat.of A) ⟶ ((baseChange b).obj G).X.left}
    (hg : g ≫ ((baseChange b).obj G).X.hom = 𝟙 _)
    (d : RelativeIdentityComponent.SectionIdentityNeighbourhoodData ((baseChange b).obj G) g t)
    (htrans : PointwiseSchemeAction.IsTransporter
      ((exponentIso (Spec (CommRingCat.of A)) I e).hom ≫
        RelativeCocharacterCentralizer.baseChangedTorusHom I G i b)
      (RelativeCocharacterCentralizer.baseChangedTorusHom I G i b)
      (show Over.mk (𝟙 _) ⟶ ((baseChange b).obj G).X from Over.homMk g hg)) :
    IdentityComponentReductiveOpenNeighbourhood G s := by
  let H := (baseChange b).obj G
  let j := RelativeCocharacterCentralizer.baseChangedTorusHom I G i b
  have hj : IsClosedSubgroup j := isClosedSubgroup_affineBaseChangedTorusHom I G i b hi
  have hselft : t ∈ geometricSelfCentralizingTorusLocus I H j := by
    rw [geometricSelfCentralizingTorusLocus_affineBaseChange I G i b hi]
    change b t ∈ geometricSelfCentralizingTorusLocus I G i
    rwa [hbt]
  have hrootst : ∀ a : I → ℤ,
      a ∈ geometricExponentRoots I H j t ↔ a = m ∨ a = -m := by
    intro a
    rw [geometricExponentRoots_affineBaseChange I G i b, hbt]
    exact hroots a
  have hdim (a : I → ℤ) :
      Module.finrank (AlgebraicClosure ((Spec (CommRingCat.of A)).residueField t))
        (weightSpace (T := commGroupScheme _ I) (geometricIdentityComponentHom I H j t)
          (exponentCharacter _ I a)) = exponentWeightRank I G i a s := by
    rw [finrank_weight_geometricIdentityComponentHom,
      exponentWeightRank_affineBaseChange I G i b, hbt]
  let d' := rankOneIdentityComponentReductiveNeighbourhood I H j hj t hselft m hm hrootst
    ((hdim m).trans hpos) ((hdim (-m)).trans hneg) e he hg d htrans
  let : Etale b := hb
  have out : IdentityComponentReductiveOpenNeighbourhood G (b t) :=
    identityComponentReductiveOpenNeighbourhood_of_openMap G b b.isOpenMap t
      d'.neighbourhood.isOpen d'.mem_neighbourhood d'.subset_locus
  exact hbt ▸ out

end Langlands.GroupScheme.splitTorus
