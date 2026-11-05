import Langlands.Geometry.Building.ParahoricBuildingAxioms
import Langlands.Geometry.Building.ApartmentRootCover
import Langlands.GroupScheme.Rational.RootFactorPairConsequences

/-! # The affine action of an actual opposite factor pair -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building

private theorem eval_sub_zsmul_char {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    (a b : characterLattice S) (z : ℤ) (w : V S) :
    eval S (a - z • b) w = eval S a w - (z : ℝ) * eval S b w := by
  rw [eval_eq_pair, eval_eq_pair, eval_eq_pair, TensorProduct.tmul_sub,
    TensorProduct.tmul_smul, map_sub, map_zsmul, LinearMap.sub_apply,
    LinearMap.smul_apply, zsmul_eq_mul]

namespace ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (B : ValuationBuildingData G)
    {α : relativeRoots B.i} {g : rationalPoints G}
    {p : rationalPoints G × rationalPoints G}

/-- The class of the integral coroot supplied by the actual opposite pair. -/
def reflectionCoroot (hg : g ∈ B.rootGroup α) (hg1 : g ≠ 1)
    (hp : RelativeRoot.IsOppositeFactorPair B.i (α : characterLattice B.S) g p) :
    TranslationSpace B.i :=
  Submodule.Quotient.mk ((1 : ℝ) ⊗ₜ[ℤ]
    hp.coroot B.i B.isMaximalSplitTorus.isSplitSubtorus.1 α.property.1 hg hg1)

/-- The derivative of the root functional takes value two on the actual pair coroot. -/
theorem rootForm_reflectionCoroot (hg : g ∈ B.rootGroup α) (hg1 : g ≠ 1)
    (hp : RelativeRoot.IsOppositeFactorPair B.i (α : characterLattice B.S) g p) :
    rootForm B.i α (B.reflectionCoroot hg hg1 hp) = 2 := by
  simp only [reflectionCoroot, rootForm_mk, eval_tmul, one_mul]
  exact_mod_cast (hp.coroot_spec B.i B.isMaximalSplitTorus.isSplitSubtorus.1
    α.property.1 hg hg1).1

/-- The linear part of the actual normalizer action is the reflection with this coroot. -/
theorem translationAction_reflectionElement (hg : g ∈ B.rootGroup α) (hg1 : g ≠ 1)
    (hp : RelativeRoot.IsOppositeFactorPair B.i (α : characterLattice B.S) g p)
    (w : TranslationSpace B.i) :
    translationAction B.i (B.reflectionElement hp) w =
      w - rootForm B.i α w • B.reflectionCoroot hg hg1 hp := by
  let ν := hp.coroot B.i B.isMaximalSplitTorus.isSplitSubtorus.1 α.property.1 hg hg1
  obtain ⟨hν, hr⟩ := hp.coroot_spec B.i B.isMaximalSplitTorus.isSplitSubtorus.1
    α.property.1 hg hg1
  let m := B.reflectionElement hp
  have hr' : ∀ χ, weylAction B.i m χ = χ - latticePairing B.S χ ν • α.val := hr
  have h2 : ∀ χ, weylAction B.i m (weylAction B.i m χ) = χ := by
    intro χ
    rw [hr', hr', map_sub, map_zsmul, LinearMap.sub_apply, LinearMap.smul_apply, hν,
      smul_eq_mul]
    module
  have hinv : ∀ χ, weylAction B.i m⁻¹ χ = χ - latticePairing B.S χ ν • α.val := by
    intro χ
    calc
      weylAction B.i m⁻¹ χ =
          weylAction B.i m⁻¹ (weylAction B.i m (weylAction B.i m χ)) := by rw [h2]
      _ = weylAction B.i m χ := by
        rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one,
          LinearEquiv.coe_one, id]
      _ = _ := hr' χ
  refine Submodule.Quotient.induction_on _ w fun v => ?_
  rw [translationAction_mk]
  change (Submodule.Quotient.mk (m • v) : TranslationSpace B.i) =
    Submodule.Quotient.mk v - eval B.S α.val v •
      Submodule.Quotient.mk ((1 : ℝ) ⊗ₜ[ℤ] ν)
  rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_sub, Submodule.Quotient.eq]
  refine mem_rootAnnihilator.2 fun b _ => ?_
  rw [map_sub, map_sub, eval_normalizer_smul, hinv, eval_sub_zsmul_char,
    map_smul, eval_tmul, one_mul]
  ring

/-- The fixed-hyperplane form of AS 1 and the actual linear action determine the full
affine action of a supplied opposite pair. -/
theorem normalizerAffineEquiv_reflectionElement_of_hasRootReflections
    (hR : B.HasRootReflections) (hg : g ∈ B.rootGroup α) (hg1 : g ≠ 1)
    (hp : RelativeRoot.IsOppositeFactorPair B.i (α : characterLattice B.S) g p) :
    B.apartment.normalizerAffineEquiv (B.reflectionElement hp) =
      AffineRootSystem.affineReflection (B.reflectionFunctional α g)
        (B.rootForm_reflectionCoroot hg hg1 hp) := by
  have hlin :
      (B.apartment.normalizerAffineEquiv (B.reflectionElement hp)).toAffineMap.linear =
        (AffineRootSystem.affineReflection (B.reflectionFunctional α g)
          (B.rootForm_reflectionCoroot hg hg1 hp)).toAffineMap.linear := by
    apply LinearMap.ext
    intro w
    change translationAction B.i (B.reflectionElement hp) w =
      Module.reflection (B.rootForm_reflectionCoroot hg hg1 hp) w
    rw [Module.reflection_apply]
    exact B.translationAction_reflectionElement hg hg1 hp w
  have hne : (B.reflectionFunctional α g).linear ≠ 0 := by
    intro h0
    have h := B.rootForm_reflectionCoroot hg hg1 hp
    change (B.reflectionFunctional α g).linear _ = 2 at h
    rw [h0, LinearMap.zero_apply] at h
    norm_num at h
  obtain ⟨x, hx⟩ := AffineRootSystem.exists_apply_eq_zero hne
  apply AffineEquiv.toAffineMap_injective
  refine AffineMap.ext_linear hlin (p := x) ?_
  have hxH : x ∈ B.reflectionHyperplane α g := by
    rw [B.reflectionHyperplane_eq hg hg1]
    exact hx
  change B.reflectionElement hp • x = _
  rw [hR α g hg hg1 p hp x hxH]
  exact (AffineRootSystem.affineReflection_apply_of_mem
    (B.reflectionFunctional α g) (B.rootForm_reflectionCoroot hg hg1 hp) hx).symm

/-- The coroot of an actual pair preserves the published affine-root system. The
root functional itself is only required to be in the extended root system. -/
theorem isCoroot_reflectionCoroot_of_hasRootReflections
    (hA : B.SatisfiesApartmentAxioms) (hR : B.HasRootReflections)
    (hg : g ∈ B.rootGroup α) (hg1 : g ≠ 1)
    (hp : RelativeRoot.IsOppositeFactorPair B.i (α : characterLattice B.S) g p) :
    AffineRootSystem.IsCoroot B.affineRoots (B.reflectionFunctional α g)
      (B.reflectionCoroot hg hg1 hp) := by
  refine ⟨B.rootForm_reflectionCoroot hg hg1 hp, fun f hf => ?_⟩
  have hm := (hA.range_le_extendedAffineWeylGroup
    ⟨B.reflectionElement hp, rfl⟩).1
  rw [B.normalizerAffineEquiv_reflectionElement_of_hasRootReflections hR hg hg1 hp] at hm
  have hf' := (hm f).2 hf
  change f.comp (AffineRootSystem.affineReflection (B.reflectionFunctional α g)
    (B.rootForm_reflectionCoroot hg hg1 hp) : B.Apartment →ᵃ[ℝ] B.Apartment) ∈
      B.affineRoots at hf'
  exact (AffineRootSystem.comp_affineReflection (B.reflectionFunctional α g)
    (B.rootForm_reflectionCoroot hg hg1 hp) f) ▸ hf'

/-- Every coroot supplied for the same functional equals the actual pair coroot. -/
theorem reflectionCoroot_eq_of_isCoroot_of_hasRootReflections
    (hA : B.SatisfiesApartmentAxioms) (hR : B.HasRootReflections)
    (hg : g ∈ B.rootGroup α) (hg1 : g ≠ 1)
    (hp : RelativeRoot.IsOppositeFactorPair B.i (α : characterLattice B.S) g p)
    {v : TranslationSpace B.i}
    (hv : AffineRootSystem.IsCoroot B.affineRoots (B.reflectionFunctional α g) v) :
    B.reflectionCoroot hg hg1 hp = v :=
  hA.isAffineRootSystem_affineRoots.isCoroot_unique
    (B.isCoroot_reflectionCoroot_of_hasRootReflections hA hR hg hg1 hp) hv

/-- The actual normalizer representative realizes the reflection defined using any
affine-root-system coroot for its functional. -/
theorem normalizerAffineEquiv_reflectionElement_eq_of_isCoroot_of_hasRootReflections
    (hA : B.SatisfiesApartmentAxioms) (hR : B.HasRootReflections)
    (hg : g ∈ B.rootGroup α) (hg1 : g ≠ 1)
    (hp : RelativeRoot.IsOppositeFactorPair B.i (α : characterLattice B.S) g p)
    {v : TranslationSpace B.i}
    (hv : AffineRootSystem.IsCoroot B.affineRoots (B.reflectionFunctional α g) v) :
    B.apartment.normalizerAffineEquiv (B.reflectionElement hp) =
      AffineRootSystem.affineReflection (B.reflectionFunctional α g) hv.1 := by
  have hv' := B.reflectionCoroot_eq_of_isCoroot_of_hasRootReflections
    hA hR hg hg1 hp hv
  simpa only [hv'] using
    B.normalizerAffineEquiv_reflectionElement_of_hasRootReflections hR hg hg1 hp

end ValuationBuildingData

namespace ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G)
    {α : relativeRoots P.i} {g : rationalPoints G}
    {p : rationalPoints G × rationalPoints G}

/-- The actual product of the supplied opposite pair lies in the actual simply
connected image. This uses root-group lifting for both signs of the root. -/
theorem reflectionElement_mem_simplyConnectedImage
    (hA : P.SatisfiesApartmentAxioms) (hg : g ∈ P.rootGroup α) (hg1 : g ≠ 1)
    (hp : RelativeRoot.IsOppositeFactorPair P.i (α : characterLattice P.S) g p) :
    (P.reflectionElement hp : rationalPoints G) ∈ P.simplyConnectedImage := by
  have hneg : -α.val ∈ relativeRoots P.i := by
    rw [← hp.weylAction_eq_neg P.i P.isMaximalSplitTorus.isSplitSubtorus.1
      α.property.1 hg hg1]
    exact weylAction_mapsTo_relativeRoots P.i (P.reflectionElement hp) α.property
  exact P.simplyConnectedImage.mul_mem
    (P.simplyConnectedImage.mul_mem
      (P.rootGroup_le_simplyConnectedImage hA _ hneg hp.1)
      (P.rootGroup_le_simplyConnectedImage hA _ α.property hg))
    (P.rootGroup_le_simplyConnectedImage hA _ hneg hp.2.1)

end ParahoricBuildingData

end Langlands.Geometry.Building
