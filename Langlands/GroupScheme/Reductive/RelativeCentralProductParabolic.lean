import Langlands.GroupScheme.RelativeLevi.NormalParabolicIntersectionSmooth
import Langlands.GroupScheme.Reductive.CentralProductParabolicIntersection
import Langlands.GroupScheme.Reductive.CentralProductParabolicInverse
import Langlands.GroupScheme.Reductive.MultiplicationBaseChange
import Langlands.GroupScheme.CentralIsogeny.BaseChange
import Langlands.GroupScheme.SubgroupFunctor.EtaleLocality

/-! # Relative parabolic intersections in a central product -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {Z D G P : GroupScheme S}

/-- Every central homomorphism factors through every relative parabolic of a
reductive group scheme. -/
theorem IsRelativeParabolicSubgroup.central_range_le
    (hG : IsReductive G) (i : P ⟶ G) (hi : IsRelativeParabolicSubgroup i)
    (z : Z ⟶ G) (hz : IsCentral z) :
    SubgroupFunctor.range z ≤ SubgroupFunctor.range i := by
  let : Mono i.hom.hom := hi.mono
  obtain ⟨𝒰, h𝒰⟩ := relativeParabolicEtaleLocalDynamic S G P i hG hi
  apply (SubgroupFunctor.le_range_iff_baseChange_etaleCover_sameUniverse 𝒰 i).mpr
  intro k
  rw [← SubgroupFunctor.range_baseChangeHom, ← SubgroupFunctor.range_baseChangeHom]
  obtain ⟨χ, hχ⟩ := h𝒰 k
  rw [hχ.2]
  exact ((isCentral_iff_range_le_center _).mp (hz.baseChange (𝒰.f k))).trans
    ((center_le_dynamicCentralizer χ).trans (Dynamic.centralizer_le_parabolic χ))

namespace CentralProductParabolic

/-- The actual intersection with a reductive normal closed factor of a central
product is a relative parabolic over every base scheme. -/
theorem isRelativeParabolicSubgroup_intersection
    (hG : IsReductive G) (hD : IsReductive D)
    (d : D ⟶ G) (hd : IsClosedSubgroup d) (hn : (SubgroupFunctor.range d).IsNormal)
    (z : Z ⟶ G) (hz : IsCentral z)
    (hprod : IsCentralIsogeny (prodHom z d (hz.commute_values _)))
    (i : P ⟶ G) (hi : IsRelativeParabolicSubgroup i) :
    IsRelativeParabolicSubgroup (subgroupIntersectionFst d i) := by
  let : IsAffineHom D.X.hom := hD.isAffineHom
  let : Smooth D.X.hom := hD.smooth
  let hc : IsClosedImmersion (subgroupIntersectionFst d i).hom.hom.left :=
    isClosedSubgroup_subgroupIntersectionFst d (relativeParabolicClosed S G P i hG hi)
  have ha : IsAffineHom (subgroupIntersection d i).X.hom := by
    rw [← Over.w (subgroupIntersectionFst d i).hom.hom]
    infer_instance
  refine ⟨RelativeLevi.smooth_normal_parabolicIntersection hG d hd hn i hi,
    ha, Over.mono_of_mono_left _, ?_⟩
  intro s
  let b := S.fromSpecResidueField s
  have hz' : IsCentral ((baseChange b).map z) := hz.baseChange b
  have hp : IsCentralIsogeny
      (prodHom ((baseChange b).map z) ((baseChange b).map d) (hz'.commute_values _)) :=
    (isCentralIsogeny_baseChange_prodHom_iff b z d (hz.commute_values _)
      (hz'.commute_values _)).mp (hprod.baseChange b)
  have hf := isParabolicSubgroup_intersection
    (hG.isConnectedReductive_residueFiber s) (hD.isConnectedReductive_residueFiber s)
    ((baseChange b).map d) (hd.baseChange b) ((baseChange b).map z) hz' hp
    ((baseChange b).map i) (hi.residueFiber s)
  have ht := hf.iso_comp (subgroupIntersectionBaseChangeIso b d i)
  change IsParabolicSubgroup ((baseChange b).map (subgroupIntersectionFst d i))
  convert ht using 1
  exact (PreservesPullback.iso_hom_fst (baseChange b) d i).symm

/-- The central product map onto an ambient relative parabolic, restricted to
its actual intersection with the reductive factor. -/
def relativeIntersectionFactor
    (hG : IsReductive G) (i : P ⟶ G) (hi : IsRelativeParabolicSubgroup i)
    (z : Z ⟶ G) (hz : IsCentral z) (d : D ⟶ G) :
    Z ⊗ subgroupIntersection d i ⟶ P :=
  let _ : Mono i.hom.hom := hi.mono
  centralProductIntersectionFactor z hz d i (hi.central_range_le hG i z hz)

/-- The restricted central multiplication is a central isogeny. -/
theorem isCentralIsogeny_relativeIntersectionFactor
    (hG : IsReductive G) (i : P ⟶ G) (hi : IsRelativeParabolicSubgroup i)
    (z : Z ⟶ G) (hz : IsCentral z) (d : D ⟶ G)
    (hprod : IsCentralIsogeny (prodHom z d (hz.commute_values _))) :
    IsCentralIsogeny (relativeIntersectionFactor hG i hi z hz d) := by
  let : Mono i.hom.hom := hi.mono
  exact isCentralIsogeny_centralProductIntersectionFactor z hz d hprod i
    (hi.central_range_le hG i z hz)

/-- The factor is the actual multiplication map after inclusion in the ambient
group. -/
theorem relativeIntersectionFactor_comp
    (hG : IsReductive G) (i : P ⟶ G) (hi : IsRelativeParabolicSubgroup i)
    (z : Z ⟶ G) (hz : IsCentral z) (d : D ⟶ G) :
    relativeIntersectionFactor hG i hi z hz d ≫ i =
      prodHom z (subgroupIntersectionHom d i) (hz.commute_values _) := by
  let : Mono i.hom.hom := hi.mono
  exact centralProductIntersectionFactor_comp z hz d i (hi.central_range_le hG i z hz)

end CentralProductParabolic
end Langlands.GroupScheme
