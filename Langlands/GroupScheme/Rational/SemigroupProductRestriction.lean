import Langlands.GroupScheme.Rational.RootProductStatement
import Langlands.GroupScheme.Rational.SemigroupPartition
import Langlands.GroupScheme.Rational.WeightSupportCongruence

/-! # Ordered semigroup products after restricting the occurring support -/

noncomputable section
universe u v w
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

namespace WeightPartition

/-- On any smaller support, restricting the original blocks does not change
membership in their positive closures under exact cross-exclusion. -/
theorem closure_restrict_support_iff {M : Type v} [Add M] {I : Type w}
    {Ψ : I → Set M} {Ω Ω' : Set M}
    (hcover : (⋃ r, Ψ r) = Ω)
    (hcross : ∀ r s : I, r ≠ s →
      Disjoint (Ψ r) (AddSubsemigroup.closure (Ψ s) : Set M))
    (hsub : Ω' ⊆ Ω) (r : I) {χ : M} (hχ : χ ∈ Ω') :
    χ ∈ AddSubsemigroup.closure (Ψ r ∩ Ω') ↔
      χ ∈ AddSubsemigroup.closure (Ψ r) := by
  constructor
  · intro hmem
    exact AddSubsemigroup.closure_mono
      (show Ψ r ∩ Ω' ⊆ Ψ r from Set.inter_subset_left) hmem
  · intro hmem
    have hblock : χ ∈ Ψ r := by
      rw [← closure_inter_support hcover hcross r]
      exact ⟨hmem, hsub hχ⟩
    exact AddSubsemigroup.subset_closure ⟨hblock, hχ⟩

end WeightPartition

section Action

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

/-- The exact ordered semigroup-product property for one supplied action. -/
def HasOrderedSemigroupProducts (b : AutomorphicAction S.toGrp G) : Prop :=
  ∀ (n : ℕ) (Ψ : Fin n → Set (characterLattice S)),
    (⋃ r, Ψ r) = actionWeightSupport b ⊤ →
    (∀ r s : Fin n, r ≠ s → Disjoint (Ψ r) (Ψ s)) →
    (∀ r s : Fin n, r ≠ s →
      Disjoint (Ψ r) (AddSubsemigroup.closure (Ψ s) : Set (characterLattice S))) →
    ∃ (H : Fin n → GroupScheme (Spec (CommRingCat.of k))) (j : ∀ r, H r ⟶ G),
      (∀ r, (semigroupSubgroup b (AddSubsemigroup.closure (Ψ r))).IsRepresentedBy (j r) ∧
        IsClosedSubgroup (j r) ∧ Smooth (H r).X.hom ∧ ConnectedSpace (H r).X.left) ∧
      IsIso (orderedMultiplication j)

/-- For an action whose support lies in the partitioned support, restriction of
the blocks preserves the actual generated subgroup functors. -/
theorem semigroupSubgroup_closure_restrict_support
    (b : AutomorphicAction S.toGrp G) {I : Type v}
    (Ψ : I → Set (characterLattice S)) (Ω : Set (characterLattice S))
    (hcover : (⋃ r, Ψ r) = Ω)
    (hcross : ∀ r s : I, r ≠ s →
      Disjoint (Ψ r) (AddSubsemigroup.closure (Ψ s) : Set (characterLattice S)))
    (hsub : actionWeightSupport b ⊤ ⊆ Ω) (r : I) :
    semigroupSubgroup b (AddSubsemigroup.closure (Ψ r ∩ actionWeightSupport b ⊤)) =
      semigroupSubgroup b (AddSubsemigroup.closure (Ψ r)) := by
  apply semigroupSubgroup_eq_of_weightSupport
  intro χ hχ
  exact WeightPartition.closure_restrict_support_iff hcover hcross hsub r hχ

/-- Ordered products for all partitions of an action's own support also apply
to unchanged blocks of a partition of any larger support. -/
theorem HasOrderedSemigroupProducts.for_larger_support
    {b : AutomorphicAction S.toGrp G} (hb : HasOrderedSemigroupProducts b)
    (Ω : Set (characterLattice S)) (hsub : actionWeightSupport b ⊤ ⊆ Ω)
    (n : ℕ) (Ψ : Fin n → Set (characterLattice S))
    (hcover : (⋃ r, Ψ r) = Ω)
    (hdis : ∀ r s : Fin n, r ≠ s → Disjoint (Ψ r) (Ψ s))
    (hcross : ∀ r s : Fin n, r ≠ s →
      Disjoint (Ψ r) (AddSubsemigroup.closure (Ψ s) : Set (characterLattice S))) :
    ∃ (H : Fin n → GroupScheme (Spec (CommRingCat.of k))) (j : ∀ r, H r ⟶ G),
      (∀ r, (semigroupSubgroup b (AddSubsemigroup.closure (Ψ r))).IsRepresentedBy (j r) ∧
        IsClosedSubgroup (j r) ∧ Smooth (H r).X.hom ∧ ConnectedSpace (H r).X.left) ∧
      IsIso (orderedMultiplication j) := by
  obtain ⟨H, j, hj, hp⟩ := hb n (fun r => Ψ r ∩ actionWeightSupport b ⊤)
    (WeightPartition.restricted_cover hcover hsub)
    (fun r s hrs => (hdis r s hrs).mono Set.inter_subset_left Set.inter_subset_left)
    (WeightPartition.restricted_cross_exclusion hcross (actionWeightSupport b ⊤))
  refine ⟨H, j, fun r => ?_, hp⟩
  have he := semigroupSubgroup_closure_restrict_support b Ψ Ω hcover hcross hsub r
  have hr := hj r
  rw [he] at hr
  exact hr

end Action

end Langlands.GroupScheme.RelativeRoot
