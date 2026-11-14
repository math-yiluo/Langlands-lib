import Langlands.Geometry.Building.UnramifiedZeroTransport
import Langlands.Geometry.Building.UnramifiedZeroIndependenceProof
import Langlands.Geometry.Building.ZeroSubgroupCommutatorNormality
import Langlands.GroupScheme.Rational.TorusCentralizerConjugacy
import Langlands.GroupScheme.Rational.MaximalSplitTorusConjugacyProof
import Langlands.GroupScheme.Rational.ParabolicPointConjugation

/-! # Independence of downstairs zero subgroups from all datum choices -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.Geometry.Building

namespace UnramifiedZeroDatum

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {H H' : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))}

/-- Transport the zero datum through an isomorphism of its ambient group. -/
def isoTransport (E : UnramifiedZeroDatum F H) (f : H ≅ H') :
    UnramifiedZeroDatum F H' where
  T := E.T
  i := E.i ≫ f.hom
  isMaximallySplitMaximalTorus := by
    obtain ⟨hT, A, a, q, ha, hq⟩ := E.isMaximallySplitMaximalTorus
    exact ⟨hT.comp_iso f, A, a ≫ f.hom, q, ha.comp_iso f, by
      rw [← Category.assoc, hq]⟩
  L := E.L
  isSplitTorus := E.isSplitTorus
  D := E.D
  C := E.C
  d := E.d ≫ f.hom
  π := E.π
  isSimplyConnectedDerivedCover :=
    ⟨E.isSimplyConnectedDerivedCover.isConnectedReductive.of_iso f.symm,
      E.isSimplyConnectedDerivedCover.isDerivedSubgroup.comp_iso f,
      E.isSimplyConnectedDerivedCover.isSimplyConnectedCover⟩

/-- The zero subgroup of the transported datum is the original subgroup's image. -/
theorem zeroPoints_isoTransport (E : UnramifiedZeroDatum F H) (f : H ≅ H') :
    (E.isoTransport f).zeroPoints = E.zeroPoints.map (rationalPoints.map f.hom) := by
  have hsc : (E.isoTransport f).simplyConnectedImage =
      E.simplyConnectedImage.map (rationalPoints.map f.hom) :=
    (map_simplyConnectedImage_eq E.isSimplyConnectedDerivedCover
      (E.isoTransport f).isSimplyConnectedDerivedCover f).symm
  rw [zeroPoints, zeroPoints, Subgroup.map_sup, hsc, Subgroup.map_map]
  congr 1

/-- Every ambient isomorphism identifies the actual zero subgroups, for every
choice of the supplied data on both sides. -/
theorem map_zeroPoints_eq_of_iso
    (E : UnramifiedZeroDatum F H) (E' : UnramifiedZeroDatum F H') (f : H ≅ H') :
    E.zeroPoints.map (rationalPoints.map f.hom) = E'.zeroPoints := by
  rw [← E.zeroPoints_isoTransport f]
  exact unramifiedZeroPointsIndependence F H' (E.isoTransport f) E'

end UnramifiedZeroDatum

/-- Isomorphisms preserve the preimages used to define anisotropic zero points,
independently of the upstairs zero datum. -/
theorem map_mem_anisotropicZeroPoints_of_iso
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {M M' : GroupScheme (Spec (CommRingCat.of F))}
    (E : UnramifiedZeroDatum F (baseChanged F (UnramifiedClosure F) M))
    (E' : UnramifiedZeroDatum F (baseChanged F (UnramifiedClosure F) M'))
    (f : M ≅ M') {z : rationalPoints M} (hz : z ∈ anisotropicZeroPoints E) :
    rationalPoints.map f.hom z ∈ anisotropicZeroPoints E' := by
  rw [mem_anisotropicZeroPoints, rationalExtend_map]
  rw [← E.map_zeroPoints_eq_of_iso E'
    ((GroupScheme.baseChange (baseMap F (UnramifiedClosure F))).mapIso f)]
  exact ⟨rationalExtend F (UnramifiedClosure F) M z, hz, rfl⟩

namespace ZeroSubgroupDatum

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S S' : CommGroupScheme (Spec (CommRingCat.of F))}
  {G Z Z' : GroupScheme (Spec (CommRingCat.of F))}
  {i : S.toGrp ⟶ G} {i' : S'.toGrp ⟶ G} {j : Z ⟶ G} {j' : Z' ⟶ G}
  (E : ZeroSubgroupDatum i j) (E' : ZeroSubgroupDatum i' j')

/-- The downstairs zero subgroup is contained in that of every other datum.
Rational conjugacy compares the split tori; normality removes the conjugation. -/
theorem zeroSubgroup_le_of_datum :
    E.zeroSubgroup ≤ E'.zeroSubgroup := by
  obtain ⟨g, e, he⟩ :=
    (maximalSplitTorusConjugacy F G E.isSimplyConnectedDerivedCover.isConnectedReductive).1
      S S' i i' E.isMaximalSplitTorus E'.isMaximalSplitTorus
  let f : G ≅ G := G.innerIso g
  have hcentral : (torusCentralizer i').comap f.hom = torusCentralizer i :=
    (torusCentralizer_eq_comap_of_iso_square i i' e f he).symm
  let q : Z ≅ Z' := E.isRepresentedBy.isoOfComap E'.isRepresentedBy f hcentral
  have hq : q.hom ≫ j' = j ≫ f.hom :=
    E.isRepresentedBy.isoOfComap_hom_comp E'.isRepresentedBy f hcentral
  apply sup_le
  · have hsc : E.simplyConnectedImage = E'.simplyConnectedImage :=
      Building.simplyConnectedImage_eq E.isSimplyConnectedDerivedCover
        E'.isSimplyConnectedDerivedCover
    rw [hsc]
    exact E'.simplyConnectedImage_le_zeroSubgroup
  · rintro _ ⟨z, hz, rfl⟩
    have hz' : rationalPoints.map q.hom z ∈ E'.centralizerZero :=
      map_mem_anisotropicZeroPoints_of_iso E.centralizerDatum E'.centralizerDatum q hz
    have hmem : rationalPoints.map f.hom (rationalPoints.map j z) ∈ E'.zeroSubgroup := by
      rw [← rationalPoints.map_comp_apply, ← hq, rationalPoints.map_comp_apply]
      exact E'.map_centralizerZero_le_zeroSubgroup ⟨rationalPoints.map q.hom z, hz', rfl⟩
    change rationalPoints.map (G.innerIso g).hom (rationalPoints.map j z) ∈
      E'.zeroSubgroup at hmem
    rw [rationalPoints_map_innerIso] at hmem
    change g * rationalPoints.map j z * g⁻¹ ∈ E'.zeroSubgroup at hmem
    have h := E'.normal_zeroSubgroup.conj_mem _ hmem g⁻¹
    simpa only [inv_inv, mul_assoc, inv_mul_cancel_left, mul_inv_cancel_right,
      inv_mul_cancel, mul_one] using h

/-- The actual downstairs zero subgroup is independent of all supplied choices. -/
theorem zeroSubgroup_eq_of_datum :
    E.zeroSubgroup = E'.zeroSubgroup :=
  le_antisymm (E.zeroSubgroup_le_of_datum E') (E'.zeroSubgroup_le_of_datum E)

end ZeroSubgroupDatum

end Langlands.Geometry.Building
