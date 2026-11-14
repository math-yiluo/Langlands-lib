import Langlands.Geometry.Building.AffineSimpleDerivativeLattice
import Langlands.Geometry.Building.AffineIrreducibleSimpleRoots
import Langlands.Geometry.Building.AffineChamberVertexSimpleRoots
import Langlands.GroupScheme.SimplyConnected.AffineCartanTransitiveShape

/-! # Integral simple-gradient generation after deleting an affine node -/

noncomputable section

universe uV uA

namespace Langlands.Geometry.Building.AffineRootSystem

open GalleryGeometry

variable {V : Type uV} {A : Type uA}
  [AddCommGroup V] [Module ℝ V] [AddTorsor V A]
  {Ψ : Set (A →ᵃ[ℝ] ℝ)}

/-- After deleting `δ`, the remaining simple affine gradients are real-linearly
independent and have the same integer span as all full derivative roots. -/
def IsIntegralSimpleDerivativeDeletion (Ψ : Set (A →ᵃ[ℝ] ℝ)) (C : Set A)
    (δ : simpleAffineRoots Ψ C) : Prop :=
  LinearIndependent ℝ (fun η : {η : simpleAffineRoots Ψ C // η ≠ δ} =>
    (η.val : A →ᵃ[ℝ] ℝ).linear) ∧
  Submodule.span ℤ (Set.range (fun η : {η : simpleAffineRoots Ψ C // η ≠ δ} =>
    (η.val : A →ᵃ[ℝ] ℝ).linear)) = Submodule.span ℤ (derivativeRoots Ψ)

namespace IsAffineRootSystemWithRankZero

variable (hΨ : IsAffineRootSystemWithRankZero Ψ)
include hΨ

/-- The full coroot form is positive definite, including on dual vectors which
are not themselves roots. -/
theorem corootForm_self_eq_zero_iff (α : Module.Dual ℝ V) :
    hΨ.corootForm α α = 0 ↔ α = 0 := by
  constructor
  · intro hα
    have hvan : ∀ v ∈ corootSet Ψ, α v = 0 := by
      intro v hv
      have h := (Finset.sum_eq_zero_iff_of_nonneg
        (fun w _ => mul_self_nonneg (α w))).mp hα v
        (hΨ.finite_corootSet.mem_toFinset.mpr hv)
      exact mul_self_eq_zero.mp h
    have hle : Submodule.span ℝ (Set.range hΨ.derivativePairing.coroot) ≤
        LinearMap.ker α := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨a, rfl⟩
      exact hvan _ ⟨hΨ.derivativeRootLift a, hΨ.derivativeRootLift_mem a,
        hΨ.isCoroot_derivativeCoroot a⟩
    rw [RootPairing.IsRootSystem.span_coroot_eq_top] at hle
    ext v
    exact hle Submodule.mem_top
  · rintro rfl
    simp [corootForm]

/-- A real left-kernel vector of the chamber Cartan matrix gives a zero
combination of the simple affine gradients. -/
theorem sum_smul_linear_eq_zero_of_leftKernel
    {C : Set A} [Fintype (simpleAffineRoots Ψ C)]
    (a : simpleAffineRoots Ψ C → ℝ)
    (ha : ∀ η : simpleAffineRoots Ψ C,
      ∑ ψ, a ψ * (ψ : A →ᵃ[ℝ] ℝ).linear
        (corootVector Ψ (η : A →ᵃ[ℝ] ℝ)) = 0) :
    ∑ ψ, a ψ • (ψ : A →ᵃ[ℝ] ℝ).linear = 0 := by
  let α : Module.Dual ℝ V := ∑ ψ, a ψ • (ψ : A →ᵃ[ℝ] ℝ).linear
  have hαη : ∀ η : simpleAffineRoots Ψ C,
      hΨ.corootForm α (η : A →ᵃ[ℝ] ℝ).linear = 0 := by
    intro η
    have h := hΨ.two_mul_corootForm (hΨ.isCoroot_corootVector_of_mem η.2.1.1) α
    have heval : α (corootVector Ψ (η : A →ᵃ[ℝ] ℝ)) = 0 := by
      simpa only [α, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] using ha η
    rw [heval, zero_mul] at h
    linarith
  apply (hΨ.corootForm_self_eq_zero_iff α).mp
  change (hΨ.corootBilin α) (∑ ψ, a ψ • (ψ : A →ᵃ[ℝ] ℝ).linear) = 0
  simp only [map_sum, map_smul,
    smul_eq_mul, corootBilin_apply, hαη, mul_zero, Finset.sum_const_zero]

/-- Matrix transitivity forces the unit-coefficient relation on simple
affine gradients. -/
theorem sum_simple_linear_eq_zero_of_matrix_transitive
    {c : A} (hc : IsRegular Ψ c)
    [Fintype (simpleAffineRoots Ψ (facet Ψ c))]
    (htrans : Langlands.GroupScheme.AffineCartan.IsVertexTransitive
      (chamberCartanMatrix Ψ (facet Ψ c))) :
    ∑ ψ : simpleAffineRoots Ψ (facet Ψ c),
      (ψ : A →ᵃ[ℝ] ℝ).linear = 0 := by
  obtain ⟨m, hm, hmker⟩ := hΨ.exists_pos_vecMul_chamberCartanMatrix_eq_zero hc
  have hcol := Langlands.GroupScheme.AffineCartan.colSum_eq_zero_of_isVertexTransitive
    (chamberCartanMatrix Ψ (facet Ψ c)) htrans m hm hmker
  have h := hΨ.sum_smul_linear_eq_zero_of_leftKernel (fun _ => 1) (by
    intro η
    have hη : ((∑ ψ, chamberCartanMatrix Ψ (facet Ψ c) ψ η : ℤ) : ℝ) = 0 := by
      rw [hcol η, Int.cast_zero]
    push_cast at hη
    simpa only [one_mul, hΨ.cast_chamberCartanMatrix] using hη)
  simpa only [one_smul] using h

omit hΨ in
/-- Every simple affine gradient belongs to the lattice generated after
deleting one node when their unweighted sum vanishes. -/
theorem simple_linear_mem_span_deleted
    {C : Set A} [Fintype (simpleAffineRoots Ψ C)]
    (hsum : ∑ ψ : simpleAffineRoots Ψ C, (ψ : A →ᵃ[ℝ] ℝ).linear = 0)
    (δ ψ : simpleAffineRoots Ψ C) :
    (ψ : A →ᵃ[ℝ] ℝ).linear ∈
      Submodule.span ℤ (Set.range (fun η : {η : simpleAffineRoots Ψ C // η ≠ δ} =>
        (η.val : A →ᵃ[ℝ] ℝ).linear)) := by
  classical
  let L := Submodule.span ℤ
    (Set.range (fun η : {η : simpleAffineRoots Ψ C // η ≠ δ} =>
      (η.val : A →ᵃ[ℝ] ℝ).linear))
  by_cases hψ : ψ = δ
  · subst ψ
    have hrest : ∑ η ∈ (Finset.univ : Finset (simpleAffineRoots Ψ C)).erase δ,
        (η : A →ᵃ[ℝ] ℝ).linear ∈ L := by
      apply L.sum_mem
      intro η hη
      exact Submodule.subset_span ⟨⟨η, Finset.ne_of_mem_erase hη⟩, rfl⟩
    have hrel := Finset.add_sum_erase (Finset.univ : Finset (simpleAffineRoots Ψ C))
      (fun η => (η : A →ᵃ[ℝ] ℝ).linear) (Finset.mem_univ δ)
    rw [hsum] at hrel
    have heq : (δ : A →ᵃ[ℝ] ℝ).linear =
        -(∑ η ∈ (Finset.univ : Finset (simpleAffineRoots Ψ C)).erase δ,
          (η : A →ᵃ[ℝ] ℝ).linear) := eq_neg_of_add_eq_zero_left hrel
    rw [heq]
    exact L.neg_mem hrest
  · exact Submodule.subset_span ⟨⟨ψ, hψ⟩, rfl⟩

/-- For an irreducible system with a vertex-transitive chamber matrix,
deleting any one simple affine root leaves an independent family generating
the full derivative lattice, provided all derivatives were integrally
generated by all the affine simple gradients. -/
theorem isIntegralSimpleDerivativeDeletion_of_matrix_transitive
    {c : A} (hc : IsRegular Ψ c) (hirr : IsIrreducibleRoots Ψ)
    (htrans : Langlands.GroupScheme.AffineCartan.IsVertexTransitive
      (chamberCartanMatrix Ψ (facet Ψ c)))
    (hspan : HasIntegralSimpleDerivativeSpan Ψ (facet Ψ c))
    (δ : simpleAffineRoots Ψ (facet Ψ c)) :
    IsIntegralSimpleDerivativeDeletion Ψ (facet Ψ c) δ := by
  classical
  let := (finite_simpleAffineRoots hΨ hc).fintype
  have hsum := hΨ.sum_simple_linear_eq_zero_of_matrix_transitive hc htrans
  have hli := hΨ.linearIndependent_simpleAffineRoots hirr hc
  have hrel : ∑ ψ : simpleAffineRoots Ψ (facet Ψ c),
      (1 : ℝ) • (ψ : A →ᵃ[ℝ] ℝ).linear = 0 := by
    simpa only [one_smul] using hsum
  refine ⟨linearIndependent_linear_ne hli hrel
    (fun h => one_ne_zero (congrFun h δ)) one_ne_zero, ?_⟩
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨η, rfl⟩
    exact Submodule.subset_span ⟨η.val.val, η.val.2.1.1, rfl⟩
  · refine Submodule.span_le.mpr fun a ha => ?_
    have hle : simpleDerivativeLattice Ψ (facet Ψ c) ≤
        Submodule.span ℤ
          (Set.range (fun η : {η : simpleAffineRoots Ψ (facet Ψ c) // η ≠ δ} =>
            (η.val : A →ᵃ[ℝ] ℝ).linear)) := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨ψ, hψ, rfl⟩
      exact simple_linear_mem_span_deleted hsum δ ⟨ψ, hψ⟩
    exact hle (hspan ha)

/-- Indivisible lifts supply the integral-generation premise of the
node-deletion theorem. -/
theorem isIntegralSimpleDerivativeDeletion_of_indivisible_lifts
    {c : A} (hc : IsRegular Ψ c) (hirr : IsIrreducibleRoots Ψ)
    (htrans : Langlands.GroupScheme.AffineCartan.IsVertexTransitive
      (chamberCartanMatrix Ψ (facet Ψ c)))
    (hlift : HasIndivisibleDerivativeLifts Ψ)
    (δ : simpleAffineRoots Ψ (facet Ψ c)) :
    IsIntegralSimpleDerivativeDeletion Ψ (facet Ψ c) δ :=
  hΨ.isIntegralSimpleDerivativeDeletion_of_matrix_transitive hc hirr htrans
    (hΨ.hasIntegralSimpleDerivativeSpan_of_indivisible_lifts hc hlift) δ

end IsAffineRootSystemWithRankZero

end Langlands.Geometry.Building.AffineRootSystem
