import Langlands.GroupScheme.SimplyConnected.InnerTypeARankOneReduction
import Langlands.GroupScheme.SimplyConnected.InnerTypeANormOneProof
import Langlands.GroupScheme.SimplyConnected.MatrixNormOneSplitRankProof

/-! # Degree-preserving binary presentations for inner type A of split rank one -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A binary norm-one presentation whose division degree retains the absolute
rank of the supplied actual inner-type-A index. -/
def DegreePreservingBinaryNormOnePresentation (K : Type u) [Field K]
    (G : GroupScheme (Spec (CommRingCat.of K))) (n : ℕ) :=
  {p : BinaryNormOnePresentation K G //
    2 * Langlands.CentralSimple.reducedDegree K p.divisionAlgebra = n + 1}

/-- The published inner-type-A presentation and matrix split-rank formula
construct a binary model, retaining its division degree, over every field. -/
theorem nonempty_degreePreservingBinaryNormOnePresentation
    {K : Type u} [Field K]
    (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G) (n : ℕ)
    (hsc : IsSimplyConnected G) (ha : IsAbsolutelyAlmostSimple G)
    (htype : d.HasInnerTypeA n) (hG : splitRank G = 1) :
    Nonempty (DegreePreservingBinaryNormOnePresentation K G n) := by
  obtain ⟨A, hA, hKA, hfd, hcentral, hsimple, hdegree, ⟨e⟩⟩ :=
    innerTypeANormOne K G d n hsc ha htype
  obtain ⟨m, hm, D, hD, hKD, hDfd, hDc, eA, ⟨f⟩⟩ :=
    CentralSimpleUnits.exists_matrix_division_model K A
  have hrank : ((m - 1 : ℕ) : ℕ∞) = 1 :=
    (CentralSimpleUnits.matrixNormOneSplitRank K D m).symm.trans
      ((splitRank_eq_of_iso (e.trans f)).symm.trans hG)
  have hm2 : m = 2 := by
    have h := ENat.natCast_inj.mp hrank
    have hpos := NeZero.ne m
    omega
  subst m
  have hdim := eA.toLinearEquiv.finrank_eq
  simp only [Module.finrank_matrix, Fintype.card_fin] at hdim
  have hdeg : 2 * Langlands.CentralSimple.reducedDegree K D = n + 1 := by
    calc
      2 * Langlands.CentralSimple.reducedDegree K D =
          Nat.sqrt ((2 * Langlands.CentralSimple.reducedDegree K D) *
            (2 * Langlands.CentralSimple.reducedDegree K D)) :=
        (Nat.sqrt_eq _).symm
      _ = Nat.sqrt (Module.finrank K A) := by
        congr 1
        rw [hdim, Langlands.CentralSimple.finrank_eq_reducedDegree_mul_self K D]
        ring
      _ = n + 1 := hdegree
  let q : BinaryNormOnePresentation K G := {
    divisionAlgebra := D
    iso := e.trans f }
  exact ⟨⟨q, hdeg⟩⟩

/-- Choose the actual degree-preserving binary presentation without any
unproved structural premise. -/
def innerTypeARankOnePresentation
    {K : Type u} [Field K]
    (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G) (n : ℕ)
    (hsc : IsSimplyConnected G) (ha : IsAbsolutelyAlmostSimple G)
    (htype : d.HasInnerTypeA n) (hG : splitRank G = 1) :
    DegreePreservingBinaryNormOnePresentation K G n :=
  Classical.choice (nonempty_degreePreservingBinaryNormOnePresentation G d n hsc ha htype hG)

/-- A rank-one inner-type-A index has odd absolute rank, equal to twice the
positive degree of an actual binary division-algebra model minus one. -/
theorem innerTypeARankOne_degree
    {K : Type u} [Field K]
    (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G) (n : ℕ)
    (hsc : IsSimplyConnected G) (ha : IsAbsolutelyAlmostSimple G)
    (htype : d.HasInnerTypeA n) (hG : splitRank G = 1) :
    ∃ p : BinaryNormOnePresentation K G,
      0 < Langlands.CentralSimple.reducedDegree K p.divisionAlgebra ∧
        n = 2 * Langlands.CentralSimple.reducedDegree K p.divisionAlgebra - 1 := by
  obtain ⟨p, hp⟩ := innerTypeARankOnePresentation G d n hsc ha htype hG
  exact ⟨p, Langlands.CentralSimple.reducedDegree_pos K p.divisionAlgebra, by omega⟩

end Langlands.GroupScheme
