import Langlands.GroupScheme.Rational.ClosedRootSubsetStatements
import Langlands.GroupScheme.Rational.StandardRootClosure
import Langlands.GroupScheme.Rational.RelativeRootSystemProof

/-! # The standard parabolic triple of relative roots -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace StandardRootTriple

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {i : T.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
  {R Θ : Set (characterLattice T)} {ν ζ : cocharacterLattice T}

/-- The two generated standard sets are the weak and zero loci of ζ. -/
theorem standard_sets_pairing (hR : IsRelativeRootAmbient i R)
    (hroot : HasRelativeRootSystem i) (hT : IsSplitTorus T.toGrp)
    (hν : IsGenericCocharacter i ν) (hΘ : Θ ⊆ simpleRelativeRoots i ν)
    (hζ : IsStandardCocharacter i ν Θ ζ) :
    standardParabolicRootSubset R ν Θ = {α | α ∈ R ∧ 0 ≤ latticePairing T α ζ} ∧
    standardLeviRootSubset R Θ = {α | α ∈ R ∧ latticePairing T α ζ = 0} := by
  have hΘR : Θ ⊆ R := hΘ.trans (hR.simple_subset hroot hT hν)
  have hnegΘR : {α | -α ∈ Θ} ⊆ R := by
    intro α hα
    simpa using hR.neg_mem hroot hT (hΘR hα)
  have hPclosed : IsClosedRootSubset R (standardParabolicRootSubset R ν Θ) :=
    isClosedRootSubset_rootClosure (Set.union_subset (fun _ h => h.1) hnegΘR)
  have hMclosed : IsClosedRootSubset R (standardLeviRootSubset R Θ) :=
    isClosedRootSubset_rootClosure (Set.union_subset hΘR hnegΘR)
  have hplusP : Θ ⊆ standardParabolicRootSubset R ν Θ := by
    intro α hα
    exact subset_rootClosure _ (Or.inl ⟨hΘR hα, (hΘ hα).1.2⟩)
  have hminusP : ∀ α ∈ Θ, -α ∈ standardParabolicRootSubset R ν Θ := by
    intro α hα
    exact subset_rootClosure _ (Or.inr (by simpa using hα))
  have hplusM : Θ ⊆ standardLeviRootSubset R Θ := fun _ h => subset_rootClosure _ (Or.inl h)
  have hminusM : ∀ α ∈ Θ, -α ∈ standardLeviRootSubset R Θ := by
    intro α hα
    exact subset_rootClosure _ (Or.inr (by simpa using hα))
  constructor
  · apply Set.Subset.antisymm
    · apply rootClosure_subset isClosed_nonneg
      intro α hα
      rcases hα with hpos | hneg
      · exact ⟨hpos.1, hζ.pairing_nonneg_of_positive i ν
          ⟨hR.subset_relativeRoots hpos.1, hpos.2⟩⟩
      · refine ⟨hnegΘR hneg, ?_⟩
        have := hζ.2.1 (-α) hneg
        simp only [map_neg, LinearMap.neg_apply] at this
        omega
    · intro α hα
      by_cases hzero : latticePairing T α ζ = 0
      · exact zero_mem_closed hR hroot hT hν hζ hPclosed hplusP hminusP hα.1 hzero
      · have hp := positive_of_pairing_pos hroot hT hν hζ
          (hR.subset_relativeRoots hα.1) (lt_of_le_of_ne hα.2 (Ne.symm hzero))
        exact subset_rootClosure _ (Or.inl ⟨hα.1, hp⟩)
  · apply Set.Subset.antisymm
    · apply rootClosure_subset isClosed_zero
      intro α hα
      rcases hα with hplus | hminus
      · exact ⟨hΘR hplus, hζ.2.1 α hplus⟩
      · refine ⟨hnegΘR hminus, ?_⟩
        have := hζ.2.1 (-α) hminus
        simpa using this
    · intro α hα
      exact zero_mem_closed hR hroot hT hν hζ hMclosed hplusM hminusM hα.1 hα.2

/-- The halfspace defined by an integral cocharacter in the real character space. -/
private def halfspace (ζ : cocharacterLattice T) : PointedCone ℝ (RealTorusSpace.Vstar T) where
  carrier := {x | 0 ≤ RealTorusSpace.pair T x (1 ⊗ₜ[ℤ] ζ)}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change 0 ≤ RealTorusSpace.pair T (x + y) (1 ⊗ₜ[ℤ] ζ)
    simpa using add_nonneg hx hy
  smul_mem' := by
    intro c x hx
    change 0 ≤ RealTorusSpace.pair T ((c : ℝ) • x) (1 ⊗ₜ[ℤ] ζ)
    change 0 ≤ ((RealTorusSpace.pair T).flip (1 ⊗ₜ[ℤ] ζ)) ((c : ℝ) • x)
    rw [map_smul, smul_eq_mul]
    exact mul_nonneg c.property hx

private theorem mem_halfspace (eta : cocharacterLattice T) (α : characterLattice T) :
    (1 : ℝ) ⊗ₜ[ℤ] α ∈ halfspace eta ↔ 0 ≤ latticePairing T α eta := by
  change 0 ≤ RealTorusSpace.pair T ((1 : ℝ) ⊗ₜ[ℤ] α) (1 ⊗ₜ[ℤ] eta) ↔ _
  simp

private theorem halfspace_closed (eta : cocharacterLattice T) :
    @IsClosed _ (moduleTopology ℝ (RealTorusSpace.Vstar T))
      (halfspace eta : Set (RealTorusSpace.Vstar T)) := by
  let := moduleTopology ℝ (RealTorusSpace.Vstar T)
  let f : RealTorusSpace.Vstar T →ₗ[ℝ] ℝ :=
    (RealTorusSpace.pair T).flip (1 ⊗ₜ[ℤ] eta)
  exact isClosed_le continuous_const (IsModuleTopology.continuous_of_linearMap f)

/-- Weak sign loci on roots are cut out by closed real halfspaces. -/
theorem convex_nonneg (R : Set (characterLattice T)) (eta : cocharacterLattice T) :
    IsConvexRootSubset R {α | α ∈ R ∧ 0 ≤ latticePairing T α eta} := by
  refine ⟨halfspace eta, halfspace_closed eta, ?_⟩
  ext α
  simp only [Set.mem_ofPred_eq, mem_halfspace]

/-- The zero locus is the intersection of opposite closed halfspaces. -/
theorem convex_zero (R : Set (characterLattice T)) (eta : cocharacterLattice T) :
    IsConvexRootSubset R {α | α ∈ R ∧ latticePairing T α eta = 0} := by
  let := moduleTopology ℝ (RealTorusSpace.Vstar T)
  refine ⟨halfspace eta ⊓ halfspace (-eta), (halfspace_closed eta).inter (halfspace_closed (-eta)), ?_⟩
  ext α
  simp only [Set.mem_ofPred_eq, Submodule.mem_inf, mem_halfspace, map_neg]
  constructor
  · rintro ⟨hα, hzero⟩
    exact ⟨hα, by omega, by omega⟩
  · rintro ⟨hα, hge, hle⟩
    exact ⟨hα, by omega⟩

/-- On the finite root set the strict locus is also an intersection of two closed
halfspaces: ν ≥ 0 and Bζ - ν ≥ 0 for a positive integer bound B on ν. -/
theorem convex_pos (hR : IsRelativeRootAmbient i R) (hroot : HasRelativeRootSystem i)
    (hT : IsSplitTorus T.toGrp) (hν : IsGenericCocharacter i ν)
    (hζ : IsStandardCocharacter i ν Θ ζ) :
    IsConvexRootSubset R {α | α ∈ R ∧ 0 < latticePairing T α ζ} := by
  let := moduleTopology ℝ (RealTorusSpace.Vstar T)
  obtain ⟨b, hb⟩ := ((hroot.finite_relativeRoots i hT).image
    (fun α => latticePairing T α ν)).bddAbove
  let B : ℤ := max b 1
  have hB : 0 < B := lt_of_lt_of_le (by omega) (le_max_right b 1)
  have hbound : ∀ α ∈ R, latticePairing T α ν ≤ B := by
    intro α hα
    exact (hb ⟨α, hR.subset_relativeRoots hα, rfl⟩).trans (le_max_left b 1)
  refine ⟨halfspace ν ⊓ halfspace (B • ζ - ν),
    (halfspace_closed ν).inter (halfspace_closed (B • ζ - ν)), ?_⟩
  ext α
  have hpair : latticePairing T α (B • ζ - ν) =
      B * latticePairing T α ζ - latticePairing T α ν := by simp
  simp only [Set.mem_ofPred_eq, Submodule.mem_inf, mem_halfspace, hpair]
  constructor
  · rintro ⟨hα, hp⟩
    have hpos := positive_of_pairing_pos hroot hT hν hζ (hR.subset_relativeRoots hα) hp
    have hle := hbound α hα
    refine ⟨hα, le_of_lt hpos, ?_⟩
    have hone : 1 ≤ latticePairing T α ζ := by omega
    nlinarith
  · rintro ⟨hα, hnonneg, hineq⟩
    have hne := hν α (hR.subset_relativeRoots hα)
    have hp : 0 < latticePairing T α ν := by omega
    refine ⟨hα, ?_⟩
    by_contra hn
    have hle : latticePairing T α ζ ≤ 0 := by omega
    nlinarith

end StandardRootTriple

/-- Renard V.4.2: the generated standard root sets form a parabolic triple,
with the integral-span formulas, convexity, unipotence, symmetry and recovery of Θ. -/
theorem standardParabolicRootTriple : StandardParabolicRootTripleStatement.{u} := by
  intro k _ G hG T i hi
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  intro R hR ν hν Θ hΘ
  have hroot : HasRelativeRootSystem i := relativeRootSystem k G hG T i hi
  have hT : IsSplitTorus T.toGrp := hi.isSplitSubtorus.1
  obtain ⟨ζ, hζ⟩ := hroot.exists_standardCocharacter i ν hT hν Θ hΘ
  obtain ⟨hP, hM⟩ := StandardRootTriple.standard_sets_pairing hR hroot hT hν hΘ hζ
  have hneg (α : characterLattice T) : -α ∈ R ↔ α ∈ R :=
    ⟨fun h => by simpa using hR.neg_mem hroot hT h, hR.neg_mem hroot hT⟩
  have hLevi : parabolicRootLevi (standardParabolicRootSubset R ν Θ) =
      standardLeviRootSubset R Θ := by
    ext α
    simp only [parabolicRootLevi, hP, hM, Set.mem_ofPred_eq, hneg,
      map_neg, LinearMap.neg_apply]
    constructor
    · rintro ⟨⟨hα, hz⟩, ⟨_, hnz⟩⟩
      exact ⟨hα, by omega⟩
    · rintro ⟨hα, hz⟩
      exact ⟨⟨hα, by omega⟩, hα, by omega⟩
  have hN : standardUnipotentRootSubset R ν Θ =
      {α | α ∈ R ∧ 0 < latticePairing T α ζ} := by
    ext α
    simp only [standardUnipotentRootSubset, parabolicRootUnipotent, hP,
      Set.mem_ofPred_eq, hneg, map_neg, LinearMap.neg_apply]
    constructor
    · rintro ⟨⟨hα, hz⟩, hn⟩
      refine ⟨hα, ?_⟩
      by_contra hnz
      exact hn ⟨hα, by omega⟩
    · rintro ⟨hα, hz⟩
      refine ⟨⟨hα, le_of_lt hz⟩, ?_⟩
      rintro ⟨_, hnz⟩
      omega
  have hPspan : standardParabolicRootSubset R ν Θ =
      {α | α ∈ R ∧ (0 < latticePairing T α ν ∨ α ∈ AddSubgroup.closure Θ)} := by
    rw [hP]
    ext α
    constructor
    · rintro ⟨hα, hz⟩
      refine ⟨hα, ?_⟩
      by_cases hzero : latticePairing T α ζ = 0
      · exact Or.inr ((StandardRootTriple.zero_iff_groupClosure hroot hT hν hζ
          (hR.subset_relativeRoots hα)).mp hzero)
      · exact Or.inl (StandardRootTriple.positive_of_pairing_pos hroot hT hν hζ
          (hR.subset_relativeRoots hα) (by omega))
    · rintro ⟨hα, hpos | hspan⟩
      · exact ⟨hα, hζ.pairing_nonneg_of_positive i ν
          ⟨hR.subset_relativeRoots hα, hpos⟩⟩
      · exact ⟨hα, le_of_eq ((StandardRootTriple.zero_iff_groupClosure hroot hT hν hζ
          (hR.subset_relativeRoots hα)).mpr hspan).symm⟩
  have hMspan : standardLeviRootSubset R Θ =
      {α | α ∈ R ∧ α ∈ AddSubgroup.closure Θ} := by
    rw [hM]
    ext α
    exact and_congr_right (fun hα => StandardRootTriple.zero_iff_groupClosure
      hroot hT hν hζ (hR.subset_relativeRoots hα))
  have hNconvex : IsConvexRootSubset R (standardUnipotentRootSubset R ν Θ) := by
    rw [hN]
    exact StandardRootTriple.convex_pos hR hroot hT hν hζ
  refine ⟨?_, hLevi, hPspan, hMspan, ?_, ?_, hNconvex, ?_, ?_, ?_⟩
  · constructor
    · rw [hP]
      exact StandardRootTriple.isClosed_nonneg
    · intro α hα
      rw [hP]
      exact ⟨hα.1, hζ.pairing_nonneg_of_positive i ν
        ⟨hR.subset_relativeRoots hα.1, hα.2⟩⟩
  · rw [hP]
    exact StandardRootTriple.convex_nonneg R ζ
  · rw [hM]
    exact StandardRootTriple.convex_zero R ζ
  · refine ⟨hNconvex.isClosedRootSubset, 1, ?_⟩
    intro α hα
    rw [hN] at hα
    refine ⟨α, ⟨hα.1, StandardRootTriple.positive_of_pairing_pos hroot hT hν hζ
      (hR.subset_relativeRoots hα.1) hα.2⟩, ?_⟩
    simp
  · constructor
    · rw [hM]
      exact StandardRootTriple.isClosed_zero
    · intro α hα
      rw [hM] at hα ⊢
      exact ⟨hR.neg_mem hroot hT hα.1, by simp [hα.2]⟩
  · ext α
    constructor
    · intro hα
      refine ⟨hΘ hα, ?_⟩
      rw [hP]
      exact ⟨hR.neg_mem hroot hT ((hR.simple_subset hroot hT hν) (hΘ hα)),
        by simp [hζ.2.1 α hα]⟩
    · rintro ⟨hα, hnegP⟩
      by_contra hnot
      have hpos := hζ.2.2 α hα hnot
      rw [hP] at hnegP
      have hnonneg := hnegP.2
      simp only [map_neg, LinearMap.neg_apply] at hnonneg
      omega

end Langlands.GroupScheme
