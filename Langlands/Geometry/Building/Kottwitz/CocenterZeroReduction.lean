import Langlands.Geometry.Building.Kottwitz.ReductiveMap
import Langlands.Geometry.Building.Kottwitz.KernelTransport
import Langlands.Geometry.Building.KPTorusIwahoriSurjectivityProof
import Langlands.Geometry.Building.KPTorusNormIsomorphism
import Langlands.GroupScheme.FppfQuotientComparison
import Langlands.GroupScheme.Derived.FieldBaseChangeAssembly
import Langlands.GroupScheme.SimplyConnected.SimplyConnectedFieldExtensionProof

/-! # The zero subgroup as a cocenter inverse image -/

noncomputable section
universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme GaloisPointComparison

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.Geometry.Building.Kottwitz

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {H : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))}

/-- The zero subgroup is the inverse image of the norm subgroup along a map
to an affine commutative group, for the specified defining datum. -/
def IsZeroPointsNormPreimage
    (E : UnramifiedZeroDatum F H)
    (Q : CommGroupScheme (Spec (CommRingCat.of (UnramifiedClosure F))))
    [IsAffine Q.X.left] (q : H ⟶ Q.toGrp) : Prop :=
  E.zeroPoints =
    (torusNormIwahori (UnramifiedClosure F) E.L (intermediateValuation F E.L) Q).comap
      (rationalPoints.map q)

/-- For a simply-connected-derived group the simply connected point image is
exactly the point kernel of every actual cocenter. -/
theorem simplyConnectedImage_eq_cocenter_kernel
    (E : UnramifiedZeroDatum F H) (hsc : HasSimplyConnectedDerivedGroup H)
    (Q : CommGroupScheme (Spec (CommRingCat.of (UnramifiedClosure F))))
    (q : H ⟶ Q.toGrp)
    (hq : RelativeRoot.IsFppfQuotient (derivedSubgroup H) q) :
    E.simplyConnectedImage = (rationalPoints.map q).ker := by
  obtain ⟨D, d, hd, hD⟩ := hsc
  let e : E.D ≅ D :=
    E.isSimplyConnectedDerivedCover.isDerivedSubgroup.isRepresentedBy.isoOfIsRepresentedBy
      hd.isRepresentedBy
  have hED : IsSimplyConnected E.D := hD.of_iso e
  let : IsIso E.π := hED.central_isogeny_isIso E.C E.π
    E.isSimplyConnectedDerivedCover.isSimplyConnectedCover.isSimplyConnected.isSemisimple
    E.isSimplyConnectedDerivedCover.isSimplyConnectedCover.isCentralIsogeny
  ext x
  change x ∈ Building.simplyConnectedImage E.d E.π ↔
    rationalPoints.map q x = 1
  rw [rationalPoints.map_apply, ← mem_range_kernelι_iff q x, hq.2.2.2]
  constructor
  · rintro ⟨c, rfl⟩
    exact E.isSimplyConnectedDerivedCover.range_comp_le_derivedSubgroup _
      ⟨c, rfl⟩
  · intro hx
    rw [← E.isSimplyConnectedDerivedCover.isDerivedSubgroup.2] at hx
    obtain ⟨y, hy⟩ := hx
    change y ≫ E.d.hom.hom = x at hy
    refine ⟨y ≫ (inv E.π).hom.hom, ?_⟩
    have hinv : (inv E.π).hom.hom ≫ E.π.hom.hom = 𝟙 E.D.X :=
      congrArg (fun f : E.D ⟶ E.D => f.hom.hom) (IsIso.inv_hom_id E.π)
    change (y ≫ (inv E.π).hom.hom) ≫ (E.π ≫ E.d).hom.hom = x
    calc
      _ = y ≫ ((inv E.π).hom.hom ≫ E.π.hom.hom) ≫ E.d.hom.hom := by
        simp only [Grp.comp_hom_hom, Category.assoc]
      _ = x := by rw [hinv, Category.id_comp, hy]

/-- Every supplied cocenter inherits the splitting and norm-image surjectivity
properties of the cocenter constructed in the Library. -/
theorem cocenter_torusNormIwahori_image
    (E : UnramifiedZeroDatum F H)
    (Q : CommGroupScheme (Spec (CommRingCat.of (UnramifiedClosure F))))
    (hQ : IsTorus Q.toGrp) (q : H ⟶ Q.toGrp)
    (hq : RelativeRoot.IsFppfQuotient (derivedSubgroup H) q) :
    letI : IsAffine Q.X.left := torusIsAffine (UnramifiedClosure F) Q hQ;
    IsSplitTorus (baseChanged (UnramifiedClosure F) E.L Q.toGrp) ∧
      E.torusIwahori.map (rationalPoints.map (E.i ≫ q)) =
        torusNormIwahori (UnramifiedClosure F) E.L (intermediateValuation F E.L) Q := by
  let : IsAffine Q.X.left := torusIsAffine (UnramifiedClosure F) Q hQ
  let hH := E.isSimplyConnectedDerivedCover.isConnectedReductive
  let : IsAffineHom H.X.hom := hH.isAffineHom
  let : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  obtain ⟨Q₀, q₀, hQa, hq₀, _, hT⟩ := cocenterQuotientExistence
    (UnramifiedClosure F) H E.D E.d hH
      E.isSimplyConnectedDerivedCover.isDerivedSubgroup
  let : IsAffine Q₀.X.left := hQa
  have hq' : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range E.d) q := by
    rwa [E.isSimplyConnectedDerivedCover.isDerivedSubgroup.2]
  let e : Q₀.toGrp ≅ Q.toGrp := FppfQuotientComparison.iso hq₀ hq'
  have he : q₀ ≫ e.hom = q := FppfQuotientComparison.iso_fac hq₀ hq'
  obtain ⟨hQsplit, hsurj⟩ := hT E.T E.i E.isMaximallySplitMaximalTorus.1
    E.L E.isSplitTorus
  refine ⟨(IsSplitTorus.iso_iff
    ((GroupScheme.baseChange (baseMap (UnramifiedClosure F) E.L)).mapIso e)).mp
      hQsplit, ?_⟩
  have hnorm := torusIwahoriSurjectivity F E.T Q₀
    (Additive.ofMul (E.i ≫ q₀)) E.L E.isSplitTorus hQsplit hsurj
  change E.torusIwahori.map (rationalPoints.map (E.i ≫ q₀)) = _ at hnorm
  have hmaps : rationalPoints.map (E.i ≫ q) =
      (rationalPoints.map e.hom).comp (rationalPoints.map (E.i ≫ q₀)) := by
    apply MonoidHom.ext
    intro x
    rw [← he]
    simp only [MonoidHom.comp_apply, rationalPoints.map_apply, Grp.comp_hom_hom,
      Category.assoc]
  rw [hmaps, ← Subgroup.map_map]
  change (E.torusIwahori.map (rationalPoints.map (E.i ≫ q₀))).map
      (rationalPoints.map e.hom) = _
  rw [hnorm]
  exact map_torusNormIwahori_eq_of_iso (UnramifiedClosure F) E.L
    (intermediateValuation F E.L) e

/-- The actual zero subgroup is the inverse image of the norm-defined torus
subgroup for every supplied cocenter of a simply-connected-derived group. -/
theorem zeroPoints_eq_cocenter_comap
    (E : UnramifiedZeroDatum F H) (hsc : HasSimplyConnectedDerivedGroup H)
    (Q : CommGroupScheme (Spec (CommRingCat.of (UnramifiedClosure F))))
    (hQ : IsTorus Q.toGrp) (q : H ⟶ Q.toGrp)
    (hq : RelativeRoot.IsFppfQuotient (derivedSubgroup H) q) :
    letI : IsAffine Q.X.left := torusIsAffine (UnramifiedClosure F) Q hQ;
    IsZeroPointsNormPreimage E Q q := by
  let : IsAffine Q.X.left := torusIsAffine (UnramifiedClosure F) Q hQ
  change E.zeroPoints =
    (torusNormIwahori (UnramifiedClosure F) E.L (intermediateValuation F E.L) Q).comap
      (rationalPoints.map q)
  have hker := simplyConnectedImage_eq_cocenter_kernel E hsc Q q hq
  have hnorm := (cocenter_torusNormIwahori_image E Q hQ q hq).2
  have hcomp : (rationalPoints.map q).comp (rationalPoints.map E.i) =
      rationalPoints.map (E.i ≫ q) := by
    apply MonoidHom.ext
    intro x
    simp only [MonoidHom.comp_apply, rationalPoints.map_apply, Grp.comp_hom_hom,
      Category.assoc]
  apply Eq.symm
  apply comap_eq_of_map_eq_of_kernel_le
  · rw [UnramifiedZeroDatum.zeroPoints, Subgroup.map_sup, hker,
      Subgroup.map_ker_self, bot_sup_eq, Subgroup.map_map, hcomp, hnorm]
  · rw [← hker]
    exact E.simplyConnectedImage_le_zeroPoints

/-- The property of having simply connected full derived subgroup ascends
along any field extension. -/
theorem hasSimplyConnectedDerivedGroup_baseChange
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (hsc : HasSimplyConnectedDerivedGroup G) :
    HasSimplyConnectedDerivedGroup (baseChanged k K G) := by
  obtain ⟨D, d, hd, hD⟩ := hsc
  refine ⟨baseChanged k K D, (GroupScheme.baseChange (baseMap k K)).map d,
    hd.baseChange_of_eq (baseMap k K)
      (derivedSubgroup_baseChange_eq_of_field (baseMap k K) G), ?_⟩
  exact isSimplyConnectedFieldExtension k K D hD

/-- Base change of a cocenter is still a quotient by the full derived subgroup. -/
theorem Cocenter.baseChange_isQuotient
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (c : Cocenter k G) :
    RelativeRoot.IsFppfQuotient (derivedSubgroup (baseChanged k K G))
      ((GroupScheme.baseChange (baseMap k K)).map c.quotient) := by
  rw [← derivedSubgroup_baseChange_eq_of_field (baseMap k K) G]
  exact c.isQuotient.baseChange (baseMap k K)

end Langlands.Geometry.Building.Kottwitz
