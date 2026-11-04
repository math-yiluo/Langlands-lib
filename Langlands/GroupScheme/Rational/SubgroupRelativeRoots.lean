import Langlands.GroupScheme.Rational.RelativeRootSignSupport
import Langlands.GroupScheme.Rational.ActionWeightSupport
import Langlands.GroupScheme.Rational.DynamicPositiveSemigroup
import Langlands.GroupScheme.Rational.RootSupportFiniteness

/-! # Actual relative roots supported by subgroup functors -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : S.toGrp ⟶ G)

/-- The nonzero conjugation weights with a nonzero actual tangent vector in `F`. -/
def subgroupRelativeRoots (F : SubgroupFunctor G) : Set (characterLattice S) :=
  actionWeightSupport (AutomorphicAction.conjugation i) F \ {0}

theorem mem_subgroupRelativeRoots (F : SubgroupFunctor G) (α : characterLattice S) :
    α ∈ subgroupRelativeRoots i F ↔
      α ∈ actionWeightSupport (AutomorphicAction.conjugation i) F ∧ α ≠ 0 :=
  Iff.rfl

@[simp] theorem zero_notMem_subgroupRelativeRoots (F : SubgroupFunctor G) :
    (0 : characterLattice S) ∉ subgroupRelativeRoots i F := by
  intro h
  exact h.2 rfl

theorem subgroupRelativeRoots_mono {F F' : SubgroupFunctor G} (h : F ≤ F') :
    subgroupRelativeRoots i F ⊆ subgroupRelativeRoots i F' :=
  fun _ hα => ⟨actionWeightSupport_mono (AutomorphicAction.conjugation i) h hα.1, hα.2⟩

theorem subgroupRelativeRoots_subset_relativeRoots (F : SubgroupFunctor G) :
    subgroupRelativeRoots i F ⊆ relativeRoots i := by
  intro α hα
  exact (mem_relativeRoots_iff_actionWeightSupport_conjugation_top i α).mpr
    ⟨hα.2, actionWeightSupport_mono (AutomorphicAction.conjugation i)
      (fun _ _ _ => Subgroup.mem_top _) hα.1⟩

@[simp] theorem subgroupRelativeRoots_top :
    subgroupRelativeRoots i ⊤ = relativeRoots i :=
  (relativeRoots_eq_actionWeightSupport_conjugation_top_diff_zero i).symm

theorem finite_subgroupRelativeRoots [LocallyOfFiniteType G.X.hom]
    (hS : IsSplitTorus S.toGrp) (F : SubgroupFunctor G) :
    (subgroupRelativeRoots i F).Finite :=
  (hS.finite_relativeRoots i).subset (subgroupRelativeRoots_subset_relativeRoots i F)

/-- The complete support of the actual positive dynamic subgroup. No semigroup
realization or ambient connectedness assumption is required. -/
theorem actionWeightSupport_dynamicUnipotent [Smooth G.X.hom]
    (hS : IsSplitTorus S.toGrp) (ν : cocharacterLattice S) :
    actionWeightSupport (AutomorphicAction.conjugation i)
        (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i)) =
      positiveRelativeRoots i ν := by
  rw [actionWeightSupport_eq_inter_of_hasLieImage
    (AutomorphicAction.conjugation i) (positiveSemigroup ν) _
    (dynamicUnipotent_semigroupData G S hS i ν).2.2
    (dynamicUnipotentGenerator G S hS i ν).property.2.2]
  exact actionWeightSupport_top_inter_positiveSemigroup i ν

@[simp] theorem subgroupRelativeRoots_dynamicUnipotent [Smooth G.X.hom]
    (hS : IsSplitTorus S.toGrp) (ν : cocharacterLattice S) :
    subgroupRelativeRoots i (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i)) =
      positiveRelativeRoots i ν := by
  rw [subgroupRelativeRoots, actionWeightSupport_dynamicUnipotent i hS ν]
  ext α
  constructor
  · exact fun h => h.1
  · intro h
    exact ⟨h, h.1.1⟩

/-- The intersection of the actual supports in `U` and `Uop'`. Applications
identify `Uop'` with the opposite radical of the second parabolic. -/
def intertwiningRelativeRoots (U Uop' : SubgroupFunctor G) :
    Set (characterLattice S) :=
  subgroupRelativeRoots i U ∩ subgroupRelativeRoots i Uop'

theorem intertwiningRelativeRoots_subset_relativeRoots (U Uop' : SubgroupFunctor G) :
    intertwiningRelativeRoots i U Uop' ⊆ relativeRoots i :=
  fun _ hα => subgroupRelativeRoots_subset_relativeRoots i U hα.1

theorem finite_intertwiningRelativeRoots [LocallyOfFiniteType G.X.hom]
    (hS : IsSplitTorus S.toGrp) (U Uop' : SubgroupFunctor G) :
    (intertwiningRelativeRoots i U Uop').Finite :=
  (hS.finite_relativeRoots i).subset
    (intertwiningRelativeRoots_subset_relativeRoots i U Uop')

theorem intertwiningRelativeRoots_dynamic [Smooth G.X.hom]
    (hS : IsSplitTorus S.toGrp) (ν eta : cocharacterLattice S) :
    intertwiningRelativeRoots i
        (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i))
        (Dynamic.unipotent (CommGroupScheme.groupHom (-eta) ≫ i)) =
      {α | α ∈ relativeRoots i ∧
        0 < latticePairing S α ν ∧ latticePairing S α eta < 0} := by
  rw [intertwiningRelativeRoots, subgroupRelativeRoots_dynamicUnipotent i hS,
    subgroupRelativeRoots_dynamicUnipotent i hS]
  ext α
  simp only [Set.mem_inter_iff, positiveRelativeRoots, Set.mem_ofPred_eq,
    map_neg, neg_pos]
  tauto

end Langlands.GroupScheme.RelativeRoot
