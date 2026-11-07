import Langlands.GroupScheme.Rational.IntrinsicRootCone
import Langlands.GroupScheme.Rational.RelativeRootNegationProof

/-! # Intrinsic nonnegative cones of actual parabolics -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.ParabolicRootPresentation

open RealTorusSpace

variable {k : Type u} [Field k]
  {A : CommGroupScheme (Spec (CommRingCat.of k))}
  {G M P : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}
  (r : ParabolicRootPresentation p l a)

/-- The nonnegative hull of all positive actual split-component weights. -/
def intrinsicNonnegCone : PointedCone ℝ (Vstar A) :=
  PointedCone.hull ℝ
    ((fun beta : characterLattice A => (1 : ℝ) ⊗ₜ[ℤ] beta) '' r.intrinsicPositiveRoots)

variable [LocallyOfFiniteType G.X.hom]

/-- Negation stability suffices to replace the restricted simple generators
by all intrinsic positive roots. Simple-root independence is unnecessary. -/
theorem nonnegCone_eq_intrinsicNonnegCone
    (hneg : ∀ alpha ∈ relativeRoots r.data.i, -alpha ∈ relativeRoots r.data.i) :
    r.nonnegCone = (r.intrinsicNonnegCone : Set (Vstar A)) := by
  have hcone : RootCombination.nonnegCone r.finite_restrictedRoots =
      r.intrinsicNonnegCone := by
    apply le_antisymm
    · rw [RootCombination.nonnegCone_eq_hull]
      exact Submodule.span_mono r.restrictedRoots_subset_image_intrinsicPositiveRoots
    · apply Submodule.span_le.mpr
      rintro x ⟨beta, hbeta, rfl⟩
      exact r.one_tmul_mem_nonnegCone_of_mem_intrinsicPositiveRoots hneg hbeta
  exact congrArg (fun C : PointedCone ℝ (Vstar A) => (C : Set (Vstar A))) hcone

variable [Smooth G.X.hom]

/-- With the two actual root-negation hypotheses, the nonnegative cones of
unrelated compatible presentations agree on the original split component. -/
theorem nonnegCone_eq_of_rootNegation
    (s : ParabolicRootPresentation p l a)
    (hnegr : ∀ alpha ∈ relativeRoots r.data.i, -alpha ∈ relativeRoots r.data.i)
    (hnegs : ∀ alpha ∈ relativeRoots s.data.i, -alpha ∈ relativeRoots s.data.i) :
    r.nonnegCone = s.nonnegCone := by
  rw [r.nonnegCone_eq_intrinsicNonnegCone hnegr,
    s.nonnegCone_eq_intrinsicNonnegCone hnegs]
  simp only [intrinsicNonnegCone, r.intrinsicPositiveRoots_eq s]

omit [Smooth G.X.hom] in
/-- For a connected reductive ambient group the published root-negation
theorem discharges both hypotheses, for every supplied presentation. -/
theorem nonnegCone_eq (hG : IsConnectedReductive G)
    (s : ParabolicRootPresentation p l a) :
    haveI := hG.smooth
    r.nonnegCone = s.nonnegCone := by
  have := hG.smooth
  exact r.nonnegCone_eq_of_rootNegation s
    (relativeRootNegation k G hG r.data.T r.data.i r.isCompatible.maximalSplit)
    (relativeRootNegation k G hG s.data.T s.data.i s.isCompatible.maximalSplit)

end Langlands.GroupScheme.ParabolicRootPresentation
