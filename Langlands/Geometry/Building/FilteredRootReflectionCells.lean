import Langlands.Geometry.Building.ApartmentRootReflections
import Langlands.Geometry.Building.ChamberRankOne
import Langlands.Geometry.Building.NormalizerNormOneFixerBoundedness
import Langlands.Geometry.Building.KPMinimalLeviZeroStatement

/-! # Actual reflection cells at a filtration jump -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.Plancherel

namespace Langlands.Geometry.Building

namespace ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (B : ValuationBuildingData G)
    {α : relativeRoots B.i} {ψ : B.Apartment →ᵃ[ℝ] ℝ}
    {u v : rationalPoints G} {p q : rationalPoints G × rationalPoints G}

/-- An element at the jump `ψ` has precisely `ψ` as its valuation functional. -/
theorem reflectionFunctional_eq_of_mem_diff
    (hψ : ψ.linear = rootForm B.i α)
    (hu : u ∈ B.affineRootGroup α ψ)
    (huplus : u ∉ B.apartment.affineRootGroupPlus α ψ) :
    u ∈ B.rootGroup α ∧ u ≠ 1 ∧ B.reflectionFunctional α u = ψ := by
  let x : B.Apartment := Classical.arbitrary B.Apartment
  have hmem := (KPApartmentData.mem_affineRootGroup_iff hψ x).1 hu
  have heq : x.val α u = (ψ x : WithTop ℝ) := by
    apply le_antisymm _ hmem.2
    exact not_lt.1 fun h => huplus
      ((KPApartmentData.mem_affineRootGroupPlus_iff hψ x).2 ⟨hmem.1, h⟩)
  have h1 : u ≠ 1 := by
    rintro rfl
    rw [B.val_apply_one] at heq
    exact WithTop.top_ne_coe heq
  refine ⟨hmem.1, h1, AffineMap.ext_linear (hψ.symm) (p := x) ?_⟩
  exact WithTop.coe_injective
    ((B.coe_reflectionFunctional_apply hmem.1 h1 x).trans heq)

/-- All actual opposite pairs along the same relative root have the same integral coroot. -/
theorem reflectionPair_coroot_eq
    (hu : u ∈ B.rootGroup α) (hu1 : u ≠ 1)
    (hv : v ∈ B.rootGroup α) (hv1 : v ≠ 1)
    (hp : RelativeRoot.IsOppositeFactorPair B.i (α : characterLattice B.S) u p)
    (hq : RelativeRoot.IsOppositeFactorPair B.i (α : characterLattice B.S) v q) :
    hp.coroot B.i B.isMaximalSplitTorus.isSplitSubtorus.1 α.property.1 hu hu1 =
      hq.coroot B.i B.isMaximalSplitTorus.isSplitSubtorus.1 α.property.1 hv hv1 := by
  let : Smooth G.X.hom := B.isConnectedReductive.smooth
  obtain ⟨hp2, hpw⟩ :=
    hp.coroot_spec B.i B.isMaximalSplitTorus.isSplitSubtorus.1 α.property.1 hu hu1
  obtain ⟨hq2, hqw⟩ :=
    hq.coroot_spec B.i B.isMaximalSplitTorus.isSplitSubtorus.1 α.property.1 hv hv1
  exact coroot_eq_of_weylAction B.i B.isMaximalSplitTorus.isSplitSubtorus.1
    (B.isMaximalSplitTorus.isSplitSubtorus.1.finite_relativeRoots B.i)
    (relativeRootsRestrictedCharactersSpan F G B.isConnectedReductive B.S B.i
      B.isMaximalSplitTorus)
    α.property hp2 hq2 hpw hqw

/-- The correction between actual opposite-pair representatives along one root centralizes
the entire split torus, including its central directions. -/
theorem reflectionElement_inv_mul_mem_centralizer
    (hu : u ∈ B.rootGroup α) (hu1 : u ≠ 1)
    (hv : v ∈ B.rootGroup α) (hv1 : v ≠ 1)
    (hp : RelativeRoot.IsOppositeFactorPair B.i (α : characterLattice B.S) u p)
    (hq : RelativeRoot.IsOppositeFactorPair B.i (α : characterLattice B.S) v q) :
    ((B.reflectionElement hp)⁻¹ * B.reflectionElement hq : normalizerPoints B.i).val ∈
      centralizerPoints B.i := by
  apply (B.isMaximalSplitTorus.isSplitSubtorus.1.weylAction_eq_one_iff B.i _).mp
  have heq : weylAction B.i (B.reflectionElement hp) =
      weylAction B.i (B.reflectionElement hq) := by
    apply LinearEquiv.ext
    intro χ
    unfold reflectionElement
    rw [(hp.coroot_spec B.i B.isMaximalSplitTorus.isSplitSubtorus.1
      α.property.1 hu hu1).2,
      (hq.coroot_spec B.i B.isMaximalSplitTorus.isSplitSubtorus.1
        α.property.1 hv hv1).2,
      B.reflectionPair_coroot_eq hu hu1 hv hv1 hp hq]
  rw [map_mul, map_inv, heq, inv_mul_cancel]

/-- At a fixed filtration jump the correction fixes every apartment point. -/
theorem reflectionElement_inv_mul_smul_eq
    (hu : u ∈ B.rootGroup α) (hu1 : u ≠ 1)
    (hv : v ∈ B.rootGroup α) (hv1 : v ≠ 1)
    (hp : RelativeRoot.IsOppositeFactorPair B.i (α : characterLattice B.S) u p)
    (hq : RelativeRoot.IsOppositeFactorPair B.i (α : characterLattice B.S) v q)
    (hlevel : B.reflectionFunctional α u = B.reflectionFunctional α v)
    (x : B.Apartment) :
    ((B.reflectionElement hp)⁻¹ * B.reflectionElement hq) • x = x := by
  have hcoroot : B.reflectionCoroot hu hu1 hp = B.reflectionCoroot hv hv1 hq := by
    unfold reflectionCoroot
    rw [B.reflectionPair_coroot_eq hu hu1 hv hv1 hp hq]
  have haction : B.apartment.normalizerAffineEquiv (B.reflectionElement hp) =
      B.apartment.normalizerAffineEquiv (B.reflectionElement hq) := by
    rw [B.normalizerAffineEquiv_reflectionElement hu hu1 hp,
      B.normalizerAffineEquiv_reflectionElement hv hv1 hq]
    apply AffineEquiv.ext
    intro y
    change (-B.reflectionFunctional α u y) • B.reflectionCoroot hu hu1 hp +ᵥ y =
      (-B.reflectionFunctional α v y) • B.reflectionCoroot hv hv1 hq +ᵥ y
    rw [hlevel, hcoroot]
  have hx := DFunLike.congr_fun haction x
  change B.reflectionElement hp • x = B.reflectionElement hq • x at hx
  rw [mul_smul, ← hx, inv_smul_smul]

/-- V5 places both factors of a point at the jump `ψ` in `U_{-ψ}`. -/
theorem oppositeFactors_mem_neg_affineRootGroup
    (hu : u ∈ B.rootGroup α) (hu1 : u ≠ 1)
    (hp : RelativeRoot.IsOppositeFactorPair B.i (α : characterLattice B.S) u p)
    (hlevel : B.reflectionFunctional α u = ψ) :
    p.1 ∈ B.affineRootGroup (-α.val) (-ψ) ∧
      p.2 ∈ B.affineRootGroup (-α.val) (-ψ) := by
  have hval (x : B.Apartment) : x.val α u = (ψ x : WithTop ℝ) := by
    rw [← B.coe_reflectionFunctional_apply hu hu1 x, hlevel]
  constructor
  · apply Subgroup.mem_iInf.mpr
    intro x
    have h5 := x.isValuation.opposite α α.property u hu hu1 p.1 hp.1 p.2 hp.2.1 hp.2.2
    rw [hval x] at h5
    exact ⟨hp.1, (withTop_eq_neg_of_add_eq_zero h5).ge⟩
  · apply Subgroup.mem_iInf.mpr
    intro x
    have h5 := x.isValuation.opposite_snd α.property hu hu1 hp.1 hp.2.1 hp.2.2
    rw [hval x] at h5
    exact ⟨hp.2.1, (withTop_eq_neg_of_add_eq_zero h5).ge⟩

end ValuationBuildingData

namespace ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G)

/-- The actual cell `U_{-ψ} m Z(F)^0 U_{-ψ}` on rational points, written with its
three factors and centralizer point exhibited. -/
def rootReflectionCell (a : characterLattice P.S) (ψ : P.Apartment →ᵃ[ℝ] ℝ)
    (m : normalizerPoints P.i) : Set (rationalPoints G) :=
  {v | ∃ l ∈ P.affineRootGroup (-a) (-ψ),
    ∃ z ∈ P.centralizerZero, ∃ r ∈ P.affineRootGroup (-a) (-ψ),
      l * m.val * rationalPoints.map P.centralizer.j z * r = v}

variable {α : relativeRoots P.i} {ψ : P.Apartment →ᵃ[ℝ] ℝ}
    {u v : rationalPoints G} {p q : rationalPoints G × rationalPoints G}

/-- The correction between two supplied representatives at the same jump is in the
mapped actual centralizer-zero subgroup, under the explicit cover comparison. -/
theorem reflectionElement_inv_mul_eq_centralizerZero
    (hA : P.SatisfiesApartmentAxioms)
    (hZ : P.zeroDatum.CoverImageCentralizerNormKernelStatement)
    (hu : u ∈ P.rootGroup α) (hu1 : u ≠ 1)
    (hv : v ∈ P.rootGroup α) (hv1 : v ≠ 1)
    (hp : RelativeRoot.IsOppositeFactorPair P.i (α : characterLattice P.S) u p)
    (hq : RelativeRoot.IsOppositeFactorPair P.i (α : characterLattice P.S) v q)
    (hlevel : P.reflectionFunctional α u = P.reflectionFunctional α v) :
    ∃ z ∈ P.centralizerZero, rationalPoints.map P.centralizer.j z =
      ((P.reflectionElement hp)⁻¹ * P.reflectionElement hq : normalizerPoints P.i).val := by
  have hc := P.toValuationBuildingData.reflectionElement_inv_mul_mem_centralizer
    hu hu1 hv hv1 hp hq
  rw [← torusCentralizer_carrier_base, ← P.centralizer.isRepresentedBy.2] at hc
  obtain ⟨z, hjz⟩ : ∃ z : rationalPoints P.centralizer.Z,
      rationalPoints.map P.centralizer.j z =
        ((P.reflectionElement hp)⁻¹ * P.reflectionElement hq : normalizerPoints P.i).val := by
    obtain ⟨z, hz⟩ := hc
    exact ⟨z, hz⟩
  have hsc : rationalPoints.map P.centralizer.j z ∈ P.simplyConnectedImage := by
    rw [hjz, Subgroup.coe_mul, Subgroup.coe_inv]
    exact P.simplyConnectedImage.mul_mem
      (P.simplyConnectedImage.inv_mem
        (P.reflectionElement_mem_simplyConnectedImage hA hu hu1 hp))
      (P.reflectionElement_mem_simplyConnectedImage hA hv hv1 hq)
  have hnorm : z ∈ rationalCommonNormKernel P.centralizer.Z := by
    let x : P.Apartment := Classical.arbitrary P.Apartment
    refine P.toValuationBuildingData.mem_rationalCommonNormKernel_of_smul_eq z
      (P.zeroDatum.zeroSubgroup_le_rationalCommonNormKernel
        (P.zeroDatum.simplyConnectedImage_le_zeroSubgroup hsc)) (x := x) ?_
    have hzn : P.centralizer.toNormalizer z =
        (P.reflectionElement hp)⁻¹ * P.reflectionElement hq := Subtype.ext hjz
    rw [hzn]
    exact P.toValuationBuildingData.reflectionElement_inv_mul_smul_eq
      hu hu1 hv hv1 hp hq hlevel x
  exact ⟨z, hZ ⟨hsc, hnorm⟩, hjz⟩

/-- KP 7.1.4's first inclusion, conditional on actual rank-one factorization and the
cover-image centralizer comparison. All cells use the supplied actual group data. -/
theorem affineRootGroup_diff_plus_subset_rootReflectionCell
    (hA : P.SatisfiesApartmentAxioms)
    (hZ : P.zeroDatum.CoverImageCentralizerNormKernelStatement)
    (hF : RelativeRoot.HasRankOneFactorization P.i)
    (hψ : ψ.linear = rootForm P.i α)
    (hu : u ∈ P.affineRootGroup α ψ)
    (huplus : u ∉ P.apartment.affineRootGroupPlus α ψ)
    (hp : RelativeRoot.IsOppositeFactorPair P.i (α : characterLattice P.S) u p) :
    (P.affineRootGroup α ψ : Set (rationalPoints G)) \
        (P.apartment.affineRootGroupPlus α ψ : Set (rationalPoints G)) ⊆
      P.rootReflectionCell α ψ (P.reflectionElement hp) := by
  obtain ⟨hu0, hu1, hulevel⟩ :=
    P.toValuationBuildingData.reflectionFunctional_eq_of_mem_diff hψ hu huplus
  rintro v ⟨hv, hvplus⟩
  obtain ⟨hv0, hv1, hvlevel⟩ :=
    P.toValuationBuildingData.reflectionFunctional_eq_of_mem_diff hψ hv hvplus
  obtain ⟨q, hq⟩ := (hF α α.property v hv0 hv1).1.exists
  obtain ⟨z, hz, hjz⟩ := P.reflectionElement_inv_mul_eq_centralizerZero
    hA hZ hu0 hu1 hv0 hv1 hp hq (hulevel.trans hvlevel.symm)
  obtain ⟨hqleft, hqright⟩ :=
    P.toValuationBuildingData.oppositeFactors_mem_neg_affineRootGroup hv0 hv1 hq hvlevel
  refine ⟨q.1⁻¹, (P.affineRootGroup (-α.val) (-ψ)).inv_mem hqleft,
    z, hz, q.2⁻¹, (P.affineRootGroup (-α.val) (-ψ)).inv_mem hqright, ?_⟩
  rw [hjz, Subgroup.coe_mul, Subgroup.coe_inv]
  simp only [ValuationBuildingData.coe_reflectionElement]
  group

end ParahoricBuildingData

end Langlands.Geometry.Building
