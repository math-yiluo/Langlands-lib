import Langlands.Geometry.Building.ApartmentRootReflections
import Langlands.Geometry.Building.NormalizerNormOneFixerBoundedness
import Langlands.Geometry.Building.KPMinimalLeviZeroStatement
import Langlands.Geometry.Building.SimplyConnectedImageNormal
import Langlands.Geometry.Building.IwahoriWeyl

/-! # Centralizer-zero conjugation by the simply connected normalizer image -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Plancherel

namespace Langlands.Geometry.Building.ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G)

/-- Under the explicit cover comparison, conjugation by an actual normalizer
point in the simply connected image preserves the mapped centralizer-zero subgroup. -/
theorem conj_mem_map_centralizerZero_of_mem_simplyConnectedImage
    (hZ : P.zeroDatum.CoverImageCentralizerNormKernelStatement)
    (n : normalizerPoints P.i)
    (hn : (n : rationalPoints G) ∈ P.simplyConnectedImage)
    {g : rationalPoints G}
    (hg : g ∈ P.centralizerZero.map (rationalPoints.map P.centralizer.j)) :
    (n : rationalPoints G) * g * (n : rationalPoints G)⁻¹ ∈
      P.centralizerZero.map (rationalPoints.map P.centralizer.j) := by
  obtain ⟨z, hz, rfl⟩ := hg
  let zn : normalizerPoints P.i := P.centralizer.toNormalizer z
  let c : normalizerPoints P.i := n * zn * n⁻¹ * zn⁻¹
  have hzc : rationalPoints.map P.centralizer.j z ∈ centralizerPoints P.i :=
    map_mem_centralizerPoints P.centralizer.isRepresentedBy z
  have hc : (c : rationalPoints G) ∈ centralizerPoints P.i := by
    change (n : rationalPoints G) * rationalPoints.map P.centralizer.j z *
      (n : rationalPoints G)⁻¹ * (rationalPoints.map P.centralizer.j z)⁻¹ ∈ _
    exact (centralizerPoints P.i).mul_mem
      (conj_mem_centralizerPoints P.i n.property hzc)
      ((centralizerPoints P.i).inv_mem hzc)
  rw [← torusCentralizer_carrier_base, ← P.centralizer.isRepresentedBy.2] at hc
  obtain ⟨w, hjw⟩ : ∃ w : rationalPoints P.centralizer.Z,
      rationalPoints.map P.centralizer.j w = (c : rationalPoints G) := by
    obtain ⟨w, hw⟩ := hc
    exact ⟨w, hw⟩
  have hsc : rationalPoints.map P.centralizer.j w ∈ P.simplyConnectedImage := by
    rw [hjw]
    have hconj := P.zeroDatum.simplyConnectedImage_normal.conj_mem
      (n : rationalPoints G)⁻¹ (P.simplyConnectedImage.inv_mem hn)
      (rationalPoints.map P.centralizer.j z)
    change (n : rationalPoints G) * rationalPoints.map P.centralizer.j z *
      (n : rationalPoints G)⁻¹ * (rationalPoints.map P.centralizer.j z)⁻¹ ∈ _
    simpa only [mul_assoc] using P.simplyConnectedImage.mul_mem hn hconj
  have hzn (x : P.Apartment) : zn • x = x :=
    P.isOmegaCompatible.smul_eq_self
      (P.zeroDatum.centralizerZero_le_rationalCommonNormKernel hz) x
  have hzninv (x : P.Apartment) : zn⁻¹ • x = x := by
    rw [inv_smul_eq_iff, hzn]
  have hnorm : w ∈ rationalCommonNormKernel P.centralizer.Z := by
    let x : P.Apartment := Classical.arbitrary P.Apartment
    refine P.toValuationBuildingData.mem_rationalCommonNormKernel_of_smul_eq w
      (P.zeroDatum.zeroSubgroup_le_rationalCommonNormKernel
        (P.zeroDatum.simplyConnectedImage_le_zeroSubgroup hsc)) (x := x) ?_
    have hwn : P.centralizer.toNormalizer w = c := Subtype.ext hjw
    rw [hwn]
    simp only [c, mul_smul, hzninv, hzn, smul_inv_smul]
  have hw : w ∈ P.centralizerZero := hZ ⟨hsc, hnorm⟩
  have heq : rationalPoints.map P.centralizer.j w *
      rationalPoints.map P.centralizer.j z =
        (n : rationalPoints G) * rationalPoints.map P.centralizer.j z *
          (n : rationalPoints G)⁻¹ := by
    rw [hjw]
    change (n : rationalPoints G) * rationalPoints.map P.centralizer.j z *
        (n : rationalPoints G)⁻¹ * (rationalPoints.map P.centralizer.j z)⁻¹ *
          rationalPoints.map P.centralizer.j z = _
    group
  rw [← heq]
  exact (P.centralizerZero.map (rationalPoints.map P.centralizer.j)).mul_mem
    ⟨w, hw, rfl⟩ ⟨z, hz, rfl⟩

/-- Such an actual normalizer point normalizes the full mapped centralizer-zero subgroup. -/
theorem mem_normalizer_map_centralizerZero_of_mem_simplyConnectedImage
    (hZ : P.zeroDatum.CoverImageCentralizerNormKernelStatement)
    (n : normalizerPoints P.i)
    (hn : (n : rationalPoints G) ∈ P.simplyConnectedImage) :
    (n : rationalPoints G) ∈ Subgroup.normalizer
      (P.centralizerZero.map (rationalPoints.map P.centralizer.j) :
        Set (rationalPoints G)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · exact P.conj_mem_map_centralizerZero_of_mem_simplyConnectedImage hZ n hn
  · intro hg
    have h := P.conj_mem_map_centralizerZero_of_mem_simplyConnectedImage hZ n⁻¹
      (P.simplyConnectedImage.inv_mem hn) hg
    have heq : (n : rationalPoints G)⁻¹ *
        ((n : rationalPoints G) * g * (n : rationalPoints G)⁻¹) *
          (n : rationalPoints G) = g := by group
    simpa only [Subgroup.coe_inv, inv_inv, heq] using h

/-- The actual conjugation equality in the original rational group. -/
theorem conj_map_centralizerZero_of_mem_simplyConnectedImage
    (hZ : P.zeroDatum.CoverImageCentralizerNormKernelStatement)
    (n : normalizerPoints P.i)
    (hn : (n : rationalPoints G) ∈ P.simplyConnectedImage) :
    (P.centralizerZero.map (rationalPoints.map P.centralizer.j)).map
        (MulAut.conj (n : rationalPoints G)).toMonoidHom =
      P.centralizerZero.map (rationalPoints.map P.centralizer.j) :=
  Subgroup.mem_normalizer_iff_map_conj_eq.1
    (P.mem_normalizer_map_centralizerZero_of_mem_simplyConnectedImage hZ n hn)

/-- Literal conjugation restricted to the actual mapped centralizer-zero subgroup. -/
def centralizerZeroSCNormalizerAut
    (hZ : P.zeroDatum.CoverImageCentralizerNormKernelStatement)
    (n : normalizerPoints P.i)
    (hn : (n : rationalPoints G) ∈ P.simplyConnectedImage) :
    MulAut (P.centralizerZero.map (rationalPoints.map P.centralizer.j)) :=
  ((MulAut.conj (n : rationalPoints G)).subgroupMap
    (P.centralizerZero.map (rationalPoints.map P.centralizer.j))).trans
      (MulEquiv.subgroupCongr
        (P.conj_map_centralizerZero_of_mem_simplyConnectedImage hZ n hn))

@[simp]
theorem coe_centralizerZeroSCNormalizerAut
    (hZ : P.zeroDatum.CoverImageCentralizerNormKernelStatement)
    (n : normalizerPoints P.i)
    (hn : (n : rationalPoints G) ∈ P.simplyConnectedImage)
    (g : P.centralizerZero.map (rationalPoints.map P.centralizer.j)) :
    (P.centralizerZeroSCNormalizerAut hZ n hn g : rationalPoints G) =
      (n : rationalPoints G) * g * (n : rationalPoints G)⁻¹ :=
  rfl

variable {α : relativeRoots P.i} {u : rationalPoints G}
    {p : rationalPoints G × rationalPoints G}

/-- A supplied reflection representative normalizes the actual centralizer-zero image.
The apartment premise is used only to place that representative in the cover image. -/
theorem reflectionElement_mem_normalizer_map_centralizerZero
    (hA : P.SatisfiesApartmentAxioms)
    (hZ : P.zeroDatum.CoverImageCentralizerNormKernelStatement)
    (hu : u ∈ P.rootGroup α) (hu1 : u ≠ 1)
    (hp : RelativeRoot.IsOppositeFactorPair P.i (α : characterLattice P.S) u p) :
    (P.reflectionElement hp : rationalPoints G) ∈ Subgroup.normalizer
      (P.centralizerZero.map (rationalPoints.map P.centralizer.j) :
        Set (rationalPoints G)) :=
  P.mem_normalizer_map_centralizerZero_of_mem_simplyConnectedImage hZ _
    (P.reflectionElement_mem_simplyConnectedImage hA hu hu1 hp)

end Langlands.Geometry.Building.ParahoricBuildingData
