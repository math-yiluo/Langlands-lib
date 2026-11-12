import Langlands.GroupScheme.SimplyConnected.CommutatorCoverImage
import Langlands.Geometry.Building.NormalizerZeroNormality
import Langlands.Geometry.Building.ChamberConjugateIntersectionProof

/-! # Normality of `G(F)^0` and of `Z(F)^0` from commutators in `G(F)^♮` -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

section Field

variable {k : Type u} [Field k] {G D C : GroupScheme (Spec (CommRingCat.of k))}
  {d : D ⟶ G} {π : C ⟶ D}

/-- Every commutator of `G(k)` lies in `G(k)^♮`, the image of `G_sc(k) → G(k)`. -/
theorem commutator_mem_simplyConnectedImage (h : IsSimplyConnectedDerivedCover d π)
    (x y : rationalPoints G) : x * y * x⁻¹ * y⁻¹ ∈ simplyConnectedImage d π := by
  obtain ⟨c, hc⟩ := h.exists_comp_eq_commutator x y
  exact ⟨c, hc⟩

/-- Every subgroup of `G(k)` containing `G(k)^♮` is normal, because it contains all
commutators. -/
theorem normal_of_simplyConnectedImage_le (h : IsSimplyConnectedDerivedCover d π)
    {H : Subgroup (rationalPoints G)} (hH : simplyConnectedImage d π ≤ H) : H.Normal := by
  refine ⟨fun x hx g => ?_⟩
  have hmem := H.mul_mem (hH (commutator_mem_simplyConnectedImage h g x)) hx
  simpa only [inv_mul_cancel_right] using hmem

end Field

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- `G(F)^0 = G(F)^♮ · Z(F)^0` is normal in `G(F)`, for every zero datum. -/
theorem ZeroSubgroupDatum.normal_zeroSubgroup
    {S : CommGroupScheme (Spec (CommRingCat.of F))}
    {G Z : GroupScheme (Spec (CommRingCat.of F))} {i : S.toGrp ⟶ G} {j : Z ⟶ G}
    (E : ZeroSubgroupDatum i j) : E.zeroSubgroup.Normal :=
  normal_of_simplyConnectedImage_le E.isSimplyConnectedDerivedCover
    E.simplyConnectedImage_le_zeroSubgroup

namespace ParahoricBuildingData

variable {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (P : ParahoricBuildingData G)

/-- `G(F)^0` is normal in `G(F)` for the actual building data. -/
theorem normal_zeroSubgroup : P.zeroSubgroup.Normal :=
  P.zeroDatum.normal_zeroSubgroup

/-- `Z(F)^0` is normal in `N(F)`. Normality of `G(F)^0` and the cover comparison of KP
Corollary 2.6.28 give it through `normalizerZero_normal_of_zeroSubgroup_normal`. -/
theorem normal_normalizerZero : P.normalizerZero.Normal :=
  haveI := P.normal_zeroSubgroup
  P.normalizerZero_normal_of_zeroSubgroup_normal P.zeroDatum.coverImageCentralizerNormKernel

end ParahoricBuildingData

end Langlands.Geometry.Building
