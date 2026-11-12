import Langlands.AbelianScheme.Tate.FieldTwoPowerTorsionDensityStatement
import Langlands.AbelianScheme.FieldCubePullbackStatement
import Langlands.AbelianScheme.AlgebraicallyClosedFieldAmpleExistenceStatement
import Langlands.AbelianScheme.Tate.TwoPowerTorsionClosureAbelianSchemeProof
import Langlands.AbelianScheme.Tate.TwoPowerTorsionLevelComparisonProof
import Langlands.AbelianScheme.Tate.GeometricTorsionNativeRank
import Langlands.AbelianScheme.MultiplicationDegree
import Langlands.AbelianScheme.FieldEqualDimensionClosedImmersionProof
import Langlands.AlgebraicGeometry.SmoothConnectedRelativeDimensionProof

/-! # Torsion density from the cube pullback identity and ample existence

This internal reduction derives the unchanged density target for actual two-power
torsion from the balanced cube pullback identity and ample existence over
algebraically closed fields. It does not prove either of them.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme.Tate

variable {K : Type u} [Field K]

/-- Every actual abelian scheme over a field is smooth of some relative dimension. -/
theorem exists_hasRelativeDimension (A : AbelianScheme (Spec (CommRingCat.of K))) :
    ∃ g : ℕ, A.HasRelativeDimension g := by
  have : ConnectedSpace A.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton A.X.hom
  exact Langlands.AlgebraicGeometry.smoothConnectedRelativeDimension _ _ A.X.hom
    inferInstance inferInstance

/-- Given the balanced cube pullback identity and ample existence over algebraically
closed fields, the actual `k`-torsion of a `g`-dimensional abelian variety has
`k ^ (2 * g)` elements whenever `k` is nonzero in the field. -/
theorem natCard_level_eq_of_cubePullback_of_ample [IsAlgClosed K]
    (cube : GroupScheme.FieldCubePullbackStatement.{u})
    (ample : GroupScheme.AlgebraicallyClosedFieldAmpleExistenceStatement.{u})
    (A : AbelianScheme (Spec (CommRingCat.of K))) (g : ℕ) (hg : A.HasRelativeDimension g)
    (k : ℕ) (hk : (k : K) ≠ 0) :
    Nat.card (GroupScheme.Tate.Level A.toGrp (Over.mk (𝟙 (Spec (CommRingCat.of K)))) k) =
      k ^ (2 * g) := by
  obtain ⟨H, hH⟩ := ample K A.toGrp A.smooth A.proper A.geometricallyConnected
  have : ConnectedSpace A.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton A.X.hom
  obtain ⟨y⟩ : Nonempty A.X.left := inferInstance
  rw [natCard_level_eq_multiplicationFinrank A k hk y]
  exact finrank_multiplication_eq_of_ne_zero A cube g hg H hH k hk y

/-- The balanced cube pullback identity and ample existence over algebraically closed
fields imply density of the actual two-power torsion locus. -/
def FieldTwoPowerTorsionDensityReductionStatement : Prop :=
  GroupScheme.FieldCubePullbackStatement.{u} →
  GroupScheme.AlgebraicallyClosedFieldAmpleExistenceStatement.{u} →
  FieldTwoPowerTorsionDensityStatement.{u}

/-- Realize the torsion closure as an abelian subvariety `B`, compare the `2`-torsion
counts `2 ^ (2 * dim B)` and `2 ^ (2 * dim A)`, and conclude that `B → A` is an
isomorphism. -/
theorem fieldTwoPowerTorsionDensity_reduction :
    FieldTwoPowerTorsionDensityReductionStatement.{u} := by
  intro cube ample Ω _ _ _ A
  obtain ⟨B, f, hi, hrange⟩ := twoPowerTorsionClosureAbelianScheme_exists Ω A
  have h2 : ((2 ^ 1 : ℕ) : Ω) ≠ 0 := by
    rw [pow_one, Nat.cast_ofNat]
    exact two_ne_zero
  obtain ⟨gA, hgA⟩ := exists_hasRelativeDimension A
  obtain ⟨gB, hgB⟩ := exists_hasRelativeDimension B
  have hA := natCard_level_eq_of_cubePullback_of_ample cube ample A gA hgA (2 ^ 1) h2
  have hB := natCard_level_eq_of_cubePullback_of_ample cube ample B gB hgB (2 ^ 1) h2
  have hbij := twoPowerTorsionLevelComparison Ω A B f hi
    (hrange ▸ subset_closure) 1
  have hcard := Nat.card_congr (Equiv.ofBijective _ hbij)
  rw [hA, hB, pow_one] at hcard
  have hg : gB = gA := by
    have := Nat.pow_right_injective (le_refl 2) hcard
    omega
  subst hg
  have : IsIso (hom f) := fieldEqualDimensionClosedImmersion Ω B A gB hgB hgA f hi
  rw [dense_iff_closure_eq, ← hrange]
  exact Set.range_eq_univ.mpr (hom f).surjective

end Langlands.AbelianScheme.Tate
