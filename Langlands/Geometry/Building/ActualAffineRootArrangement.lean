import Langlands.Geometry.Building.ReflectionNormalizerWeylActionFromOppositePairs
import Langlands.Geometry.Building.FiniteRealTorusSpace
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # The algebraic part of the actual affine reflection arrangement -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building

section Coordinates

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    (i : S.toGrp ⟶ G) [IsAffineHom G.X.hom]

/-- Coordinates of a reduced translation in all actual root directions. -/
def rootDerivativeCoordinates :
    TranslationSpace i →ₗ[ℝ] (relativeRoots i → ℝ) :=
  LinearMap.pi fun a => rootForm i a

@[simp]
theorem rootDerivativeCoordinates_apply (v : TranslationSpace i) (a : relativeRoots i) :
    rootDerivativeCoordinates i v a = rootForm i a v :=
  rfl

/-- The quotient by the common root annihilator is separated by root coordinates. -/
theorem eq_zero_of_rootForm_eq_zero (v : TranslationSpace i)
    (h : ∀ a : relativeRoots i, rootForm i a v = 0) : v = 0 := by
  revert h
  refine Submodule.Quotient.induction_on _ v fun w hw => ?_
  rw [Submodule.Quotient.mk_eq_zero]
  exact mem_rootAnnihilator.mpr fun a ha => hw ⟨a, ha⟩

theorem rootDerivativeCoordinates_injective :
    Function.Injective (rootDerivativeCoordinates i) := by
  intro v w h
  apply sub_eq_zero.mp
  apply eq_zero_of_rootForm_eq_zero
  intro a
  rw [map_sub]
  exact sub_eq_zero.mpr (congrFun h a)

end Coordinates

namespace ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (B : ValuationBuildingData G)

/-- Ordinary affine roots have finitely many derivative directions for the actual torus. -/
theorem finite_derivativeRoots_affineRoots :
    (AffineRootSystem.derivativeRoots B.affineRoots).Finite := by
  have : Smooth G.X.hom := B.isConnectedReductive.smooth
  let := B.isMaximalSplitTorus.isSplitSubtorus.1.finite_relativeRoots B.i |>.fintype
  refine (Set.finite_range (rootForm B.i)).subset ?_
  rintro f ⟨ψ, ⟨a, hlin, _⟩, rfl⟩
  exact ⟨a, hlin.symm⟩

variable (hF : RelativeRoot.HasOppositeFactorPairs B.i)

include hF

/-- Actual opposite pairs supply coroots for every ordinary affine root. -/
theorem exists_isCoroot_affineRoots_of_oppositePairs
    {ψ : B.Apartment →ᵃ[ℝ] ℝ} (hψ : ψ ∈ B.affineRoots) :
    ∃ v : TranslationSpace B.i, AffineRootSystem.IsCoroot B.affineRoots ψ v := by
  have hψ' := B.apartment.affineRoots_subset_extendedAffineRoots hψ
  rw [← B.reflectionAffineRoots_eq] at hψ'
  obtain ⟨a, g, hg, hg1, rfl⟩ := hψ'
  obtain ⟨p, hp⟩ := hF a a.property g hg hg1
  exact ⟨B.reflectionCoroot hg hg1 hp,
    B.isCoroot_reflectionCoroot_without_apartment_axioms hg hg1 hp⟩

/-- In particular every ordinary affine root is nonconstant. -/
theorem linear_ne_zero_affineRoots_of_oppositePairs
    {ψ : B.Apartment →ᵃ[ℝ] ℝ} (hψ : ψ ∈ B.affineRoots) :
    ψ.linear ≠ 0 := by
  obtain ⟨v, hv⟩ := B.exists_isCoroot_affineRoots_of_oppositePairs hF hψ
  intro hzero
  have h := hv.1
  rw [hzero, LinearMap.zero_apply] at h
  norm_num at h

/-- V0, hF-derived AS4 and reduced root coordinates give spanning derivatives. -/
theorem span_derivativeRoots_affineRoots_of_oppositePairs :
    Submodule.span ℝ (AffineRootSystem.derivativeRoots B.affineRoots) = ⊤ := by
  have : Module.Finite ℝ (V B.S) :=
    B.isMaximalSplitTorus.isSplitSubtorus.1.finite_realCocharacterSpace
  apply Submodule.span_eq_top_of_ne_zero
  intro v hv
  have hsep : ∃ a : relativeRoots B.i, rootForm B.i a v ≠ 0 := by
    by_contra! h
    exact hv (eq_zero_of_rootForm_eq_zero B.i v h)
  obtain ⟨a, ha⟩ := hsep
  let x : B.Apartment := Classical.arbitrary B.Apartment
  obtain ⟨g, hg, hgtop⟩ := x.isValuation.exists_ne_top a.property
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hgtop
  let ψ := B.apartment.affineFunctional a x r
  have hψ : ψ ∈ B.apartment.extendedAffineRoots :=
    B.apartment.affineFunctional_mem_extendedAffineRoots hg hr.symm
  have hlin : ψ.linear = rootForm B.i a := rfl
  rcases B.affineRoot_mem_or_two_smul_mem_of_oppositePairs hF ψ hψ with h | h
  · refine ⟨ψ.linear, AffineRootSystem.linear_mem_derivativeRoots h, ?_⟩
    rwa [hlin]
  · refine ⟨((2 : ℝ) • ψ).linear, AffineRootSystem.linear_mem_derivativeRoots h, ?_⟩
    rw [AffineMap.smul_linear, hlin, LinearMap.smul_apply]
    exact mul_ne_zero (by norm_num) ha

/-- For actual supplied data, opposite-pair existence proves all local-arrangement
laws except bounded finiteness of the ordinary affine roots. -/
theorem isLocallyFiniteReflectionArrangement_of_oppositePairs
    (hfinite : ∀ (x : B.Apartment) (bound : Module.Dual ℝ (TranslationSpace B.i) → ℝ),
      {ψ | ψ ∈ B.affineRoots ∧ |ψ x| ≤ bound ψ.linear}.Finite) :
    AffineRootSystem.IsLocallyFiniteReflectionArrangement B.affineRoots where
  span_derivativeRoots_eq_top := B.span_derivativeRoots_affineRoots_of_oppositePairs hF
  linear_ne_zero := fun _ hψ => B.linear_ne_zero_affineRoots_of_oppositePairs hF hψ
  finite_derivativeRoots := B.finite_derivativeRoots_affineRoots
  exists_isCoroot := fun _ hψ => B.exists_isCoroot_affineRoots_of_oppositePairs hF hψ
  finite_bounded_at := hfinite

end ValuationBuildingData
end Langlands.Geometry.Building
