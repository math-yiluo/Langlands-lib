import Langlands.Geometry.Building.KPLocalSplitNorm
import Langlands.Geometry.Building.MaximalUnramifiedValuation
import Langlands.Geometry.Building.ZeroSubgroupCommutatorNormality
import Langlands.GroupScheme.Rational.MaximalSplitTorusConjugacyProof
import Langlands.GroupScheme.Rational.ParabolicPointConjugation
import Langlands.GroupScheme.Torus.SplitReductiveProof

/-! # Bounded split-torus points in every unramified zero datum -/
noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme GaloisPointComparison Langlands.LocalGalois.Separable

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.Geometry.Building

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- Scalar unit norms from a finite Galois splitting field of the unramified
closure reach every unit for the normalized valuation. -/
theorem unramified_unit_norm_surjective
    (L : IntermediateField (UnramifiedClosure F) (SeparableClosure F))
    [FiniteDimensional (UnramifiedClosure F) L] [IsGalois (UnramifiedClosure F) L]
    (a : (UnramifiedClosure F)ˣ) (ha : MaximalUnramified.valuation F (a : UnramifiedClosure F) = 1) :
    ∃ b : Lˣ, intermediateValuation F L (b : L) = 1 ∧
      Units.map (Algebra.norm (UnramifiedClosure F)) b = a := by
  obtain ⟨x, hx, hxN⟩ :=
    (Langlands.ClassFieldTheory.Local.SeparableInertiaNorm.ambientHyp_sepClosureValuation F).exists_norm_eq_of_tower
      (E := UnramifiedClosure F) (L := L) (M := L) (a : UnramifiedClosure F)
        ((MaximalUnramified.valuation_isEquiv F).eq_one_iff_eq_one.mp ha)
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [map_zero, map_zero] at hx
    exact zero_ne_one hx
  exact ⟨Units.mk0 x hx0, hx, Units.ext hxN⟩

namespace UnramifiedZeroDatum

variable {F} {H : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))}
  (E : UnramifiedZeroDatum F H)

/-- The zero subgroup of any supplied datum is normal without independence of
that datum. -/
theorem normal_zeroPoints : E.zeroPoints.Normal :=
  normal_of_simplyConnectedImage_le E.isSimplyConnectedDerivedCover
    E.simplyConnectedImage_le_zeroPoints

/-- Every bounded point of a closed split subtorus maps into the zero subgroup
of any supplied datum. -/
theorem map_split_characterValuationKernel_le_zeroPoints
    (hH : IsConnectedReductive H)
    (S : CommGroupScheme (Spec (CommRingCat.of (UnramifiedClosure F))))
    (iS : S.toGrp ⟶ H) (hiS : IsSplitSubtorus iS) :
    (characterValuationKernel (MaximalUnramified.valuation F) S.toGrp).map
      (rationalPoints.map iS) ≤ E.zeroPoints := by
  have := hH.isAffineHom
  have := hH.smooth
  obtain ⟨M, j, hj, φ, hφ⟩ := exists_maximalSplitTorus_extension H iS hiS
  obtain ⟨A, a, f, ha, hf⟩ := E.isMaximallySplitMaximalTorus.2
  obtain ⟨g, e, he⟩ := (maximalSplitTorusConjugacy (UnramifiedClosure F) H hH).1
    M A j a hj ha
  have : IsAffineHom A.X.hom := ha.1.1.isAffineHom
  have : IsAffine A.X.left := isAffine_of_isAffineHom A.X.hom
  rintro _ ⟨s, hs, rfl⟩
  let t := rationalPoints.map (φ ≫ e.hom) s
  have ht : t ∈ characterValuationKernel (MaximalUnramified.valuation F) A.toGrp :=
    map_characterValuationKernel_le _ _ ⟨s, hs, rfl⟩
  have htnorm := split_kernel_le_torusNormIwahori (UnramifiedClosure F) E.L
    (MaximalUnramified.valuation F) (intermediateValuation F E.L)
    (unramified_unit_norm_surjective F E.L) A ha.1.1 ht
  have hft : rationalPoints.map f t ∈ E.torusIwahori :=
    map_torusNormIwahori_le (UnramifiedClosure F) E.L (intermediateValuation F E.L)
      (Additive.ofMul f : A ⟶ E.T) ⟨t, htnorm, rfl⟩
  have hz := E.map_torusIwahori_le_zeroPoints ⟨_, hft, rfl⟩
  have hmaps : (φ ≫ e.hom) ≫ f ≫ E.i = iS ≫ (H.innerIso g).hom := by
    rw [Category.assoc, hf, ← he, ← Category.assoc, hφ]
  have heq : rationalPoints.map E.i (rationalPoints.map f t) =
      rationalPoints.map (H.innerIso g).hom (rationalPoints.map iS s) := by
    simpa only [rationalPoints.map_apply, Grp.comp_hom_hom, Category.assoc, t] using
      congrArg (fun b => rationalPoints.map b s) hmaps
  rw [heq, rationalPoints_map_innerIso] at hz
  simpa [mul_assoc] using E.normal_zeroPoints.conj_mem _ hz g⁻¹

/-- The actual rational-point map restricted from bounded split-torus points
to the zero subgroup of the supplied datum. -/
def splitBoundedPointMap
    (hH : IsConnectedReductive H)
    (S : CommGroupScheme (Spec (CommRingCat.of (UnramifiedClosure F))))
    (iS : S.toGrp ⟶ H) (hiS : IsSplitSubtorus iS) :
    characterValuationKernel (MaximalUnramified.valuation F) S.toGrp →* E.zeroPoints :=
  ((rationalPoints.map iS).comp
    (characterValuationKernel (MaximalUnramified.valuation F) S.toGrp).subtype).codRestrict _
      (fun s => E.map_split_characterValuationKernel_le_zeroPoints hH S iS hiS
        ⟨s, s.property, rfl⟩)

end UnramifiedZeroDatum
end Langlands.Geometry.Building
