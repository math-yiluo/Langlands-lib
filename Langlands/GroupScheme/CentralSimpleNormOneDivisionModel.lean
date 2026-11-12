import Langlands.GroupScheme.CentralSimpleNormOneTransport
import Langlands.GroupScheme.CentralSimpleBinaryRoots
import Langlands.GroupScheme.Rational.SplitRankTransport
import Langlands.GroupScheme.SimplyConnected.MatrixNormOneSplitRankStatement

/-!
# Division-algebra matrix models of actual reduced-norm-one groups

Wedderburn--Artin and norm preservation give an actual group-scheme
isomorphism to a matrix norm-one group over a central division algebra.
The rank-one specialization is conditional on the published matrix-rank
statement, which is not proved here.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.CentralSimpleUnits

variable (K A : Type u) [Field K] [Ring A] [Algebra K A]
  [FiniteDimensional K A] [Algebra.IsCentral K A] [IsSimpleRing A]

/-- An actual matrix-algebra presentation, retaining the algebra equivalence
rather than a type label or a supplied group classification. -/
structure DivisionMatrixPresentation where
  size : ℕ
  [size_ne_zero : NeZero size]
  divisionAlgebra : Type u
  [divisionRing : DivisionRing divisionAlgebra]
  [algebra : Algebra K divisionAlgebra]
  [finiteDimensional : FiniteDimensional K divisionAlgebra]
  [central : Algebra.IsCentral K divisionAlgebra]
  equiv : A ≃ₐ[K] Matrix (Fin size) (Fin size) divisionAlgebra

attribute [instance] DivisionMatrixPresentation.size_ne_zero
  DivisionMatrixPresentation.divisionRing DivisionMatrixPresentation.algebra
  DivisionMatrixPresentation.finiteDimensional DivisionMatrixPresentation.central

/-- Wedderburn--Artin constructs a matrix presentation over a finite-dimensional
central division algebra. -/
def divisionMatrixPresentation : DivisionMatrixPresentation K A := Classical.choice <| by
  let : IsArtinianRing A := IsArtinianRing.of_finite K A
  obtain ⟨m, hm, D, hD, hKD, hfd, ⟨e⟩⟩ :=
    IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite K A
  let : Algebra.IsCentral K D := Langlands.CentralSimple.isCentral_of_algEquiv_matrix e
  exact ⟨⟨m, D, e⟩⟩

/-- The actual group-scheme isomorphism induced by the algebra presentation. -/
def DivisionMatrixPresentation.normOneIso (p : DivisionMatrixPresentation K A) :
    normOne K A ≅ normOne K (Matrix (Fin p.size) (Fin p.size) p.divisionAlgebra) :=
  normOneAlgEquivIso p.equiv

/-- A central simple algebra and its actual norm-one group admit simultaneous
matrix presentations over a finite-dimensional central division algebra. -/
theorem exists_matrix_division_model :
    ∃ (m : ℕ) (_ : NeZero m) (D : Type u) (_ : DivisionRing D) (_ : Algebra K D)
      (_ : FiniteDimensional K D) (_ : Algebra.IsCentral K D),
      ∃ _e : A ≃ₐ[K] Matrix (Fin m) (Fin m) D,
        Nonempty (normOne K A ≅ normOne K (Matrix (Fin m) (Fin m) D)) := by
  let p := divisionMatrixPresentation K A
  exact ⟨p.size, p.size_ne_zero, p.divisionAlgebra, p.divisionRing, p.algebra,
    p.finiteDimensional, p.central, p.equiv,
    ⟨DivisionMatrixPresentation.normOneIso K A p⟩⟩

/-- Assuming the matrix-rank formula, rank one forces the binary matrix
norm-one model. This does not assert the matrix-rank formula. -/
theorem exists_binary_model_of_splitRank_one
    (hrank : MatrixNormOneSplitRankStatement.{u}) (hA : splitRank (normOne K A) = 1) :
    ∃ (D : Type u) (_ : DivisionRing D) (_ : Algebra K D)
      (_ : FiniteDimensional K D) (_ : Algebra.IsCentral K D),
      Nonempty (normOne K A ≅ BinaryRoot.groupScheme K D) := by
  obtain ⟨m, hm, D, hD, hKD, hfd, hcentral, e, ⟨f⟩⟩ := exists_matrix_division_model K A
  have h : ((m - 1 : ℕ) : ℕ∞) = 1 :=
    (hrank K D m).symm.trans ((splitRank_eq_of_iso f).symm.trans hA)
  have hm' : m - 1 = 1 := ENat.natCast_inj.mp h
  have hm0 : m ≠ 0 := NeZero.ne m
  have hm2 : m = 2 := by omega
  subst m
  exact ⟨D, hD, hKD, hfd, hcentral, ⟨f⟩⟩

/-- The same conditional reduction applies to any actual group scheme with
a reduced-norm-one presentation. -/
theorem exists_binary_model_of_normOne_presentation
    (hrank : MatrixNormOneSplitRankStatement.{u})
    {G : GroupScheme (Spec (CommRingCat.of K))} (e : G ≅ normOne K A)
    (hG : splitRank G = 1) :
    ∃ (D : Type u) (_ : DivisionRing D) (_ : Algebra K D)
      (_ : FiniteDimensional K D) (_ : Algebra.IsCentral K D),
      Nonempty (G ≅ BinaryRoot.groupScheme K D) := by
  obtain ⟨D, hD, hKD, hfd, hcentral, ⟨f⟩⟩ :=
    exists_binary_model_of_splitRank_one K A hrank ((splitRank_eq_of_iso e).symm.trans hG)
  exact ⟨D, hD, hKD, hfd, hcentral, ⟨e.trans f⟩⟩

end Langlands.GroupScheme.CentralSimpleUnits
