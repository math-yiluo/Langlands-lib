import Langlands.Geometry.Building.ApartmentRootReflections
import Langlands.Geometry.Building.KPParahoricFixerComparison
import Langlands.GroupScheme.Rational.RootFactorizationFromExistence
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Norm-one root reflections and the apartment fixed locus at a special point -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace Langlands.Plancherel

namespace Langlands.Geometry.Building

namespace AffineRootSystem

/-- The roots vanishing at a special point separate it from every other point,
including in a root system of rank zero. -/
theorem eq_of_isSpecialPoint_of_vanishingRoots
    {V A : Type*} [AddCommGroup V] [Module ℝ V] [AddTorsor V A]
    {Ψ : Set (A →ᵃ[ℝ] ℝ)} (hΨ : IsAffineRootSystemWithRankZero Ψ)
    {x y : A} (hx : IsSpecialPoint Ψ x)
    (hy : ∀ ψ ∈ vanishingRoots Ψ x, ψ y = 0) :
    y = x := by
  have hroot : ∀ a ∈ derivativeRoots Ψ, a (y -ᵥ x) = 0 := by
    rintro a ⟨ψ, hψ, rfl⟩
    obtain ⟨f, hf, hker⟩ :=
      (isSpecialPoint_iff_ker hΨ.linear_ne_zero x).1 hx ψ hψ
    apply LinearMap.mem_ker.mp
    rw [hker, LinearMap.mem_ker, AffineMap.linearMap_vsub, hy f hf, hf.2]
    simp
  have hspan : Submodule.span ℝ (derivativeRoots Ψ) ≤
      LinearMap.ker (Module.Dual.eval ℝ V (y -ᵥ x)) :=
    Submodule.span_le.mpr hroot
  have hall : ∀ a : Module.Dual ℝ V, a (y -ᵥ x) = 0 := by
    intro a
    exact hspan (hΨ.span_derivativeRoots_eq_top.symm ▸ Submodule.mem_top)
  exact vsub_eq_zero_iff_eq.mp
    ((Module.forall_dual_apply_eq_zero_iff ℝ (y -ᵥ x)).mp hall)

end AffineRootSystem

namespace ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (B : ValuationBuildingData G)

/-- Every actual root point lies in some compact filtration, hence in the
common rational-character norm kernel under V 7. -/
theorem rootGroup_le_rationalCommonNormKernel
    (hTopo : B.apartment.IsTopologyCompatible) (a : relativeRoots B.i) :
    B.rootGroup a ≤ rationalCommonNormKernel G := by
  intro g hg
  let x : B.Apartment := Classical.arbitrary B.Apartment
  exact B.filtration_le_rationalCommonNormKernel hTopo x a ((x.val a g).untopD 0)
    (KPApartmentData.mem_filtration.mpr
      ⟨hg, WithTop.coe_untopD_le (x.val a g) 0⟩)

/-- The actual product of an opposite factor pair is norm one, without a
surjectivity premise on a central covering group. -/
theorem reflectionElement_mem_rationalCommonNormKernel
    (hTopo : B.apartment.IsTopologyCompatible)
    {a : relativeRoots B.i} {g : rationalPoints G}
    (hg : g ∈ B.rootGroup a) (hg1 : g ≠ 1)
    {p : rationalPoints G × rationalPoints G}
    (hp : RelativeRoot.IsOppositeFactorPair B.i (a : characterLattice B.S) g p) :
    (B.reflectionElement hp : rationalPoints G) ∈ rationalCommonNormKernel G := by
  have hneg : -a.val ∈ relativeRoots B.i := by
    rw [← hp.weylAction_eq_neg B.i B.isMaximalSplitTorus.isSplitSubtorus.1
      a.property.1 hg hg1]
    exact weylAction_mapsTo_relativeRoots B.i (B.reflectionElement hp) a.property
  exact (rationalCommonNormKernel G).mul_mem
    ((rationalCommonNormKernel G).mul_mem
      (B.rootGroup_le_rationalCommonNormKernel hTopo ⟨-a.val, hneg⟩ hp.1)
      (B.rootGroup_le_rationalCommonNormKernel hTopo a hg))
    (B.rootGroup_le_rationalCommonNormKernel hTopo ⟨-a.val, hneg⟩ hp.2.1)

/-- A lift of an affine root reflection to an actual norm-one normalizer point.
The action is the already defined action on the actual valuation apartment. -/
structure NormOneAffineRootReflection (ψ : B.Apartment →ᵃ[ℝ] ℝ) where
  normalizer : normalizerPoints B.i
  vector : TranslationSpace B.i
  pairing : ψ.linear vector = 2
  norm_one : (normalizer : rationalPoints G) ∈ rationalCommonNormKernel G
  action_eq : B.apartment.normalizerAffineEquiv normalizer =
    AffineRootSystem.affineReflection ψ pairing

/-- Actual opposite-pair existence and V 7 produce norm-one lifts of all
affine roots. Apartment validity and apartment injection are not used here. -/
theorem nonempty_normOneAffineRootReflection
    (hTopo : B.apartment.IsTopologyCompatible)
    (hE : RelativeRoot.HasOppositeFactorPairs B.i)
    {ψ : B.Apartment →ᵃ[ℝ] ℝ} (hψ : ψ ∈ B.affineRoots) :
    Nonempty (B.NormOneAffineRootReflection ψ) := by
  have hψ' := B.apartment.affineRoots_subset_extendedAffineRoots hψ
  rw [← B.reflectionAffineRoots_eq] at hψ'
  obtain ⟨a, g, hg, hg1, rfl⟩ := hψ'
  obtain ⟨p, hp⟩ := hE a a.property g hg hg1
  exact ⟨{
    normalizer := B.reflectionElement hp
    vector := B.reflectionCoroot hg hg1 hp
    pairing := B.rootForm_reflectionCoroot hg hg1 hp
    norm_one := B.reflectionElement_mem_rationalCommonNormKernel hTopo hg hg1 hp
    action_eq := B.normalizerAffineEquiv_reflectionElement hg hg1 hp }⟩

/-- Choose an actual norm-one lift for an affine root, retaining precisely
the topology-compatibility and opposite-pair existence premises. -/
def normOneAffineRootReflection
    (hTopo : B.apartment.IsTopologyCompatible)
    (hE : RelativeRoot.HasOppositeFactorPairs B.i)
    {ψ : B.Apartment →ᵃ[ℝ] ℝ} (hψ : ψ ∈ B.affineRoots) :
    B.NormOneAffineRootReflection ψ :=
  Classical.choice (B.nonempty_normOneAffineRootReflection hTopo hE hψ)

namespace NormOneAffineRootReflection

variable {B} {ψ : B.Apartment →ᵃ[ℝ] ℝ} (r : B.NormOneAffineRootReflection ψ)

/-- The lift lies in the existing norm-one stabilizer at every point of
the root hyperplane. -/
theorem mem_compactStabilizer {x : B.Apartment} (hx : ψ x = 0) :
    (r.normalizer : rationalPoints G) ∈ B.compactStabilizer (B.apartmentMap x) := by
  apply B.mem_compactStabilizer.mpr
  refine ⟨r.norm_one, ?_⟩
  rw [B.normalizer_smul_apartmentMap]
  change B.apartmentMap (B.apartment.normalizerAffineEquiv r.normalizer x) =
    B.apartmentMap x
  rw [r.action_eq, AffineRootSystem.affineReflection_apply_of_mem ψ r.pairing hx]

/-- Under apartment injection, a point whose apartment image is fixed by the
lift lies on its root hyperplane. -/
theorem apply_eq_zero_of_fixed
    (hinj : Function.Injective B.apartmentMap) {y : B.Apartment}
    (hy : (r.normalizer : rationalPoints G) • B.apartmentMap y = B.apartmentMap y) :
    ψ y = 0 := by
  rw [B.normalizer_smul_apartmentMap] at hy
  have hfix : AffineRootSystem.affineReflection ψ r.pairing y = y := by
    rw [← r.action_eq]
    exact hinj hy
  have h := AffineRootSystem.apply_affineReflection ψ r.pairing y
  rw [hfix] at h
  linarith

end NormOneAffineRootReflection

/-- Apartment-local uniqueness at a special point of the actual quotient.
Actual pair existence, apartment injection and the indicated root-system and
topology hypotheses remain explicit. -/
theorem eq_of_compactStabilizer_fixed_in_apartment_of_isSpecialPoint
    (hTopo : B.apartment.IsTopologyCompatible)
    (hE : RelativeRoot.HasOppositeFactorPairs B.i)
    (hRoots : AffineRootSystem.IsAffineRootSystemWithRankZero B.affineRoots)
    (hinj : Function.Injective B.apartmentMap)
    {x y : B.Apartment} (hx : AffineRootSystem.IsSpecialPoint B.affineRoots x)
    (hy : ∀ g : rationalPoints G,
      g ∈ B.compactStabilizer (B.apartmentMap x) →
        g • B.apartmentMap y = B.apartmentMap y) :
    y = x := by
  apply AffineRootSystem.eq_of_isSpecialPoint_of_vanishingRoots hRoots hx
  intro ψ hψ
  let r := B.normOneAffineRootReflection hTopo hE hψ.1
  exact r.apply_eq_zero_of_fixed hinj
    (hy r.normalizer (r.mem_compactStabilizer hψ.2))

/-- With the apartment axioms, a special point is the only point in the
base apartment image fixed by its full existing norm-one stabilizer. -/
theorem eq_of_compactStabilizer_fixed_of_isSpecialPoint
    (hA : B.SatisfiesApartmentAxioms)
    (hE : RelativeRoot.HasOppositeFactorPairs B.i)
    (hinj : Function.Injective B.apartmentMap)
    {x : B.Apartment} (hx : AffineRootSystem.IsSpecialPoint B.affineRoots x)
    {z : B.ReducedBuilding} (hz : z ∈ B.apartmentImage)
    (hfixed : ∀ g : rationalPoints G,
      g ∈ B.compactStabilizer (B.apartmentMap x) → g • z = z) :
    z = B.apartmentMap x := by
  obtain ⟨y, rfl⟩ := hz
  exact congrArg B.apartmentMap
    (B.eq_of_compactStabilizer_fixed_in_apartment_of_isSpecialPoint
      hA.topologyCompatible hE hA.isAffineRootSystem_affineRoots hinj hx hfixed)

end ValuationBuildingData

end Langlands.Geometry.Building
