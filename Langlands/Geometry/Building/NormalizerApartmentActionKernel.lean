import Langlands.Geometry.Building.IwahoriWeyl
import Langlands.Geometry.Building.KPCentralizerParahoricAssembly
import Langlands.Geometry.Building.ChamberExchange
import Langlands.Geometry.Building.NormalizerNormOneFixerBoundedness

/-! # The actual apartment-action kernel on the zero-component normalizer -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace Langlands.Plancherel

namespace Langlands.Geometry.Building

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

namespace ValuationBuildingData

variable (B : ValuationBuildingData G)

/-- For the actual maximal split torus, the reduced linear action has exactly
the centralizer kernel. -/
theorem translationAction_eq_one_iff_mem_centralizerPoints
    (n : normalizerPoints B.i) :
    translationAction B.i n = 1 ↔ (n : rationalPoints G) ∈ centralizerPoints B.i := by
  let hT := B.isMaximalSplitTorus.isSplitSubtorus.1
  constructor
  · intro hn
    have hfixed : ∀ a ∈ relativeRoots B.i, weylAction B.i n⁻¹ a = a := by
      intro a ha
      apply eval_injective hT
      apply LinearMap.ext
      intro v
      have h := congrArg
        (fun e : TranslationSpace B.i ≃ₗ[ℝ] TranslationSpace B.i =>
          rootForm B.i ⟨a, ha⟩ (e (Submodule.Quotient.mk v))) hn
      change eval B.S a (n • v) = eval B.S a v at h
      rwa [eval_normalizer_smul] at h
    have hw := hT.weylAction_eq_one_of_fixed_roots B.i
      (relativeRootsRestrictedCharactersSpan F G B.isConnectedReductive B.S B.i
        B.isMaximalSplitTorus) n⁻¹ hfixed
    have hc := (hT.weylAction_eq_one_iff B.i n⁻¹).mp hw
    simpa only [Subgroup.coe_inv, inv_inv] using (centralizerPoints B.i).inv_mem hc
  · intro hn
    apply LinearEquiv.ext
    intro v
    refine Submodule.Quotient.induction_on _ v fun w => ?_
    change Submodule.Quotient.mk (normalizerAction B.i n w) = Submodule.Quotient.mk w
    rw [normalizerAction_eq_one_of_mem_centralizerPoints B.i hn]
    rfl

/-- A normalizer point acting trivially on the actual apartment centralizes the
actual maximal split torus. -/
theorem mem_centralizerPoints_of_normalizerAffineEquiv_eq_one
    (n : normalizerPoints B.i) (hn : B.apartment.normalizerAffineEquiv n = 1) :
    (n : rationalPoints G) ∈ centralizerPoints B.i := by
  apply (B.translationAction_eq_one_iff_mem_centralizerPoints n).mp
  exact congrArg (fun e : B.Apartment ≃ᵃ[ℝ] B.Apartment => e.linear) hn

end ValuationBuildingData

namespace ParahoricBuildingData

variable (P : ParahoricBuildingData G)

/-- The original normalizer action restricted to `N(F) ∩ G(F)^0`. -/
def zeroComponentApartmentAction :
    P.normalizerZeroComponent →* (P.Apartment ≃ᵃ[ℝ] P.Apartment) :=
  P.apartment.normalizerAffineEquiv.comp P.normalizerZeroComponent.subtype

@[simp]
theorem zeroComponentApartmentAction_apply (n : P.normalizerZeroComponent) :
    P.zeroComponentApartmentAction n =
      P.apartment.normalizerAffineEquiv (n : normalizerPoints P.i) :=
  rfl

/-- Under the cover comparison, a zero-component normalizer point acts trivially
on the apartment exactly when it belongs to the original centralizer-zero subgroup. -/
theorem normalizerAffineEquiv_eq_one_iff_of_mem_normalizerZeroComponent
    (hZ : P.zeroDatum.CoverImageCentralizerNormKernelStatement)
    (n : normalizerPoints P.i) (hn : n ∈ P.normalizerZeroComponent) :
    P.apartment.normalizerAffineEquiv n = 1 ↔ n ∈ P.normalizerZero := by
  constructor
  · intro h
    have hc :=
      P.toValuationBuildingData.mem_centralizerPoints_of_normalizerAffineEquiv_eq_one n h
    rw [← torusCentralizer_carrier_base, ← P.centralizer.isRepresentedBy.2] at hc
    obtain ⟨z, hjz⟩ : ∃ z : rationalPoints P.centralizer.Z,
        rationalPoints.map P.centralizer.j z = (n : rationalPoints G) := by
      obtain ⟨z, hz⟩ := hc
      exact ⟨z, hz⟩
    have hzn : P.centralizer.toNormalizer z = n := Subtype.ext hjz
    have hzNorm : z ∈ rationalCommonNormKernel P.centralizer.Z := by
      let x : P.Apartment := Classical.arbitrary P.Apartment
      apply P.toValuationBuildingData.mem_rationalCommonNormKernel_of_smul_eq z
        (x := x)
      · rw [hjz]
        exact P.zeroDatum.zeroSubgroup_le_rationalCommonNormKernel hn
      · rw [hzn]
        exact congrArg (fun e : P.Apartment ≃ᵃ[ℝ] P.Apartment => e x) h
    have hzZero : z ∈ P.centralizerZero := by
      have hi := P.zeroDatum.centralizerZeroIntersection_of_coverImage hZ
      change P.zeroSubgroup.comap (rationalPoints.map P.centralizer.j) ⊓
        rationalCommonNormKernel P.centralizer.Z = P.centralizerZero at hi
      rw [← hi]
      refine ⟨?_, hzNorm⟩
      change rationalPoints.map P.centralizer.j z ∈ P.zeroSubgroup
      rwa [hjz]
    exact ⟨z, hzZero, hzn⟩
  · rintro ⟨z, hz, rfl⟩
    apply AffineEquiv.ext
    intro x
    exact P.isOmegaCompatible.smul_eq_self
      (P.zeroDatum.centralizerZero_le_rationalCommonNormKernel hz) x

/-- The kernel equality uses the actual subgroup of the actual normalizer. -/
theorem ker_zeroComponentApartmentAction
    (hZ : P.zeroDatum.CoverImageCentralizerNormKernelStatement) :
    P.zeroComponentApartmentAction.ker =
      P.normalizerZero.subgroupOf P.normalizerZeroComponent := by
  ext n
  exact P.normalizerAffineEquiv_eq_one_iff_of_mem_normalizerZeroComponent hZ n n.property

end ParahoricBuildingData

end Langlands.Geometry.Building
