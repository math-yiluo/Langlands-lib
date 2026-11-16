import Langlands.GroupScheme.Rational.ClosedRootSubsetStatements
import Langlands.GroupScheme.Rational.RelativeRootSystemProof
import Langlands.GroupScheme.Rational.RelativeRootMultiples
import Langlands.GroupScheme.Rational.RootSubgroupMultipleInclusion

/-! # Cone saturation from indivisible roots to all relative roots -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}

/-- Intersecting two cone slices intersects their cones. -/
theorem rootConeSlice_inf (R : Set (characterLattice T))
    (C D : PointedCone ℝ (RealTorusSpace.Vstar T)) :
    {a | a ∈ R ∧ (1 : ℝ) ⊗ₜ[ℤ] a ∈ C ⊓ D} =
      {a | a ∈ R ∧ (1 : ℝ) ⊗ₜ[ℤ] a ∈ C} ∩
        {a | a ∈ R ∧ (1 : ℝ) ⊗ₜ[ℤ] a ∈ D} := by
  ext a
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Submodule.mem_inf]
  tauto

/-- Convex root subsets are stable under intersection, for any ambient set. -/
theorem IsConvexRootSubset.inter {R S X : Set (characterLattice T)}
    (hS : IsConvexRootSubset R S) (hX : IsConvexRootSubset R X) :
    IsConvexRootSubset R (S ∩ X) := by
  obtain ⟨C, hC, rfl⟩ := hS
  obtain ⟨D, hD, rfl⟩ := hX
  let : TopologicalSpace (RealTorusSpace.Vstar T) :=
    moduleTopology ℝ (RealTorusSpace.Vstar T)
  refine ⟨C ⊓ D, ?_, (rootConeSlice_inf R C D).symm⟩
  exact hC.inter hD

/-- A positive dilation by two preserves membership in a pointed cone. -/
theorem tmul_double_mem_pointedCone_iff
    (C : PointedCone ℝ (RealTorusSpace.Vstar T)) (a : characterLattice T) :
    (1 : ℝ) ⊗ₜ[ℤ] (2 • a) ∈ C ↔ (1 : ℝ) ⊗ₜ[ℤ] a ∈ C := by
  have heq : (1 : ℝ) ⊗ₜ[ℤ] (2 • a) =
      (2 : ℝ) • ((1 : ℝ) ⊗ₜ[ℤ] a) := by
    simp only [two_nsmul, TensorProduct.tmul_add, two_smul ℝ]
  rw [heq]
  exact C.smul_mem_iff (by norm_num : (0 : ℝ) < 2)

section RootSystem

variable [IsAffineHom G.X.hom] {i : T.toGrp ⟶ G} [Mono i.hom.hom.left]

/-- Every root is indivisible or twice an indivisible root. -/
theorem HasRelativeRootSystem.mem_indivisible_or_eq_double
    (hR : HasRelativeRootSystem i) {a : characterLattice T} (ha : a ∈ relativeRoots i) :
    a ∈ RelativeRoot.indivisibleRoots i ∨
      ∃ b ∈ RelativeRoot.indivisibleRoots i, a = 2 • b := by
  by_cases hind : a ∈ RelativeRoot.indivisibleRoots i
  · exact Or.inl hind
  right
  obtain ⟨b, hb, m, hm, hma⟩ :
      ∃ b ∈ relativeRoots i, ∃ m : ℕ, 1 < m ∧ m • b = a := by
    simpa only [RelativeRoot.indivisibleRoots, Set.mem_ofPred_eq, ha, true_and,
      not_forall, not_not, exists_prop] using hind
  have hmaRoot : m • b ∈ relativeRoots i := hma ▸ ha
  have hm2 : m = 2 := by
    rcases hR.eq_one_or_two_of_nsmul_mem hb hmaRoot with h | h
    · omega
    · exact h
  subst m
  refine ⟨b, ⟨hb, ?_⟩, hma.symm⟩
  intro c hc n hn hnc
  have hroot : (2 * n) • c ∈ relativeRoots i := by
    rw [mul_smul, hnc, hma]
    exact ha
  rcases hR.eq_one_or_two_of_nsmul_mem hc hroot with h | h <;> omega

/-- Saturating an indivisible cone slice by all actual roots preserves its
minimal closed generated group, on every test scheme. -/
theorem IsRootSubsetGroup.of_indivisible_coneSlice
    (hR : HasRelativeRootSystem i) (C : PointedCone ℝ (RealTorusSpace.Vstar T))
    {H : GroupScheme (Spec (CommRingCat.of k))} {h : H ⟶ G}
    (hh : IsRootSubsetGroup i
      {a | a ∈ RelativeRoot.indivisibleRoots i ∧ (1 : ℝ) ⊗ₜ[ℤ] a ∈ C} h) :
    IsRootSubsetGroup i
      {a | a ∈ relativeRoots i ∧ (1 : ℝ) ⊗ₜ[ℤ] a ∈ C} h := by
  refine ⟨hh.1, hh.2.1, ?_, ?_⟩
  · intro a ha
    rcases hR.mem_indivisible_or_eq_double ha.1 with hind | ⟨b, hb, rfl⟩
    · exact hh.2.2.1 a ⟨hind, ha.2⟩
    · exact (RelativeRoot.double_subgroup_le i b).trans
        (hh.2.2.1 b ⟨hb, (tmul_double_mem_pointedCone_iff C b).mp ha.2⟩)
  · intro K q hq hcentral hroots
    exact hh.2.2.2 K q hq hcentral (fun a ha => hroots a ⟨ha.1.1, ha.2⟩)

end RootSystem

/-- The full-relative-root intersection theorem implies Renard's intersection
statement in the indivisible roots. This is a reduction, with its premise explicit. -/
def ConvexRootSubsetGroupIntersectionReductionStatement : Prop :=
  ClosedRootSubsetGroupIntersectionStatement.{u} →
    ConvexRootSubsetGroupIntersectionStatement.{u}

/-- Apply the full-root theorem to the same closed cones in all relative roots. -/
theorem convexRootSubsetGroupIntersection_of_closed :
    ConvexRootSubsetGroupIntersectionReductionStatement.{u} := by
  intro hclosed k _ G hG T i hi
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  have hR : HasRelativeRootSystem i := relativeRootSystem k G hG T i hi
  intro S X hS hX H₁ H₂ H₃ h₁ h₂ h₃ hh₁ hh₂ hh₃
  obtain ⟨C, hC, rfl⟩ := hS
  obtain ⟨D, hD, rfl⟩ := hX
  have hSC : IsConvexRootSubset (relativeRoots i)
      {a | a ∈ relativeRoots i ∧ (1 : ℝ) ⊗ₜ[ℤ] a ∈ C} := ⟨C, hC, rfl⟩
  have hXD : IsConvexRootSubset (relativeRoots i)
      {a | a ∈ relativeRoots i ∧ (1 : ℝ) ⊗ₜ[ℤ] a ∈ D} := ⟨D, hD, rfl⟩
  have hh₃' : IsRootSubsetGroup i
      {a | a ∈ relativeRoots i ∧ (1 : ℝ) ⊗ₜ[ℤ] a ∈ C ⊓ D} h₃ := by
    apply IsRootSubsetGroup.of_indivisible_coneSlice hR (C ⊓ D)
    rwa [rootConeSlice_inf]
  rw [rootConeSlice_inf] at hh₃'
  exact hclosed k G hG T i hi _ _ hSC.isClosedRootSubset hXD.isClosedRootSubset
    (hSC.inter hXD) H₁ H₂ H₃ h₁ h₂ h₃
    (hh₁.of_indivisible_coneSlice hR C) (hh₂.of_indivisible_coneSlice hR D) hh₃'

end Langlands.GroupScheme
