import Langlands.GroupScheme.Reductive.RankOneRootReducednessStatement
import Langlands.GroupScheme.Reductive.RankOnePositiveRootBaseChange
import Langlands.GroupScheme.Torus.MaximalBaseChangeProof

/-! # Rank-one root reducedness descends from an algebraic closure -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

/-- The algebraically closed case of rank-one reducedness, stated using the actual
adjoint roots and the prescribed split maximal torus. -/
def RankOneAlgClosedRootReducednessStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))),
    IsSplitTorus T.toGrp → ∀ i : T.toGrp ⟶ G, IsMaximalTorus i →
      haveI := hG.isAffineHom
      (∀ α ∈ roots i, ∀ β ∈ roots i, ¬ LinearIndependent ℤ ![α, β]) →
        ∀ α ∈ roots i, ∀ β ∈ roots i, α = β ∨ α = -β

/-- All-field rank-one reducedness restricts to algebraically closed fields. -/
theorem rankOneAlgClosedRootReducedness_of_statement
    (h : RankOneRootReducednessStatement.{u}) :
    RankOneAlgClosedRootReducednessStatement.{u} := by
  intro k _ _ G hG T hT i hi
  exact h k G hG T hT i hi

/-- Rank-one reducedness over algebraically closed fields suffices over every field.
The actual roots and their integral dependence are transported along character pullback. -/
theorem rankOneRootReducedness_of_algClosed
    (hclosed : RankOneAlgClosedRootReducednessStatement.{u}) :
    RankOneRootReducednessStatement.{u} := by
  intro k _ G hG T hT i hi
  have := hG.isAffineHom
  have := hG.smooth
  intro hdep α hα β hβ
  let b := toAlgebraicClosure k
  let Gc := (GroupScheme.baseChange b).obj G
  let Tc := (CommGroupScheme.baseChange b).obj T
  let ic : Tc.toGrp ⟶ Gc := (GroupScheme.baseChange b).map i
  have hGc : IsConnectedReductive Gc := hG.baseChange_toAlgebraicClosure
  have := hGc.isAffineHom
  have hic : IsMaximalTorus ic :=
    (maximalTorusBaseChange k (AlgebraicClosure k) G T i hi.1 hi.2.1).mp hi
  have hdepc : ∀ α ∈ roots ic, ∀ β ∈ roots ic,
      ¬ LinearIndependent ℤ ![α, β] :=
    (roots_pairwise_dependent_baseChange_iff (K := AlgebraicClosure k) G T hT i).mpr hdep
  have hαc := (mem_roots_baseChange_iff (K := AlgebraicClosure k) G T hT i α).mpr hα
  have hβc := (mem_roots_baseChange_iff (K := AlgebraicClosure k) G T hT i β).mpr hβ
  rcases hclosed (AlgebraicClosure k) Gc hGc Tc (hT.baseChange b) ic hic hdepc
    _ hαc _ hβc with h | h
  · exact Or.inl ((hT.characterLattice_baseChange_bijective b T).injective h)
  · right
    apply (hT.characterLattice_baseChange_bijective b T).injective
    simpa only [map_neg] using h

/-- The all-field and algebraically closed formulations of rank-one reducedness are
logically equivalent without changing the universe or the actual-root convention. -/
theorem rankOneRootReducedness_iff_algClosed :
    RankOneRootReducednessStatement.{u} ↔ RankOneAlgClosedRootReducednessStatement.{u} :=
  ⟨rankOneAlgClosedRootReducedness_of_statement, rankOneRootReducedness_of_algClosed⟩

end Langlands.GroupScheme
