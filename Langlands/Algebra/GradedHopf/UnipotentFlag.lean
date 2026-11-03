import Langlands.Algebra.GradedHopf.BigCell
import Langlands.Algebra.GradedHopf.GradedComodule
import Langlands.GroupScheme.UnipotentMatrixCriterion.HopfSpec

/-! # Upper unitriangular graded matrix coefficients of a unipotent graded Hopf algebra -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry Langlands.GroupScheme

namespace Langlands.Algebra.GradedHopf

section IsUnitriangular

variable {k A : Type*} [CommRing k] [CommRing A] [Bialgebra k A] {𝒜 : ℤ → Submodule k A}

/-- The matrix of graded matrix coefficients is upper unitriangular: its diagonal entries are `1`
and its entries below the diagonal are `0`. -/
def GradedMatrixCoefficients.IsUnitriangular (G : GradedMatrixCoefficients 𝒜) : Prop :=
  (∀ i, G.M i i = 1) ∧ ∀ i j, j < i → G.M i j = 0

theorem GradedMatrixCoefficients.isUnitriangular_iff (G : GradedMatrixCoefficients 𝒜) :
    G.IsUnitriangular ↔ (∀ i, G.M i i = 1) ∧ ∀ i j, j < i → G.M i j = 0 :=
  Iff.rfl

end IsUnitriangular

/-- If the group scheme of a finitely generated `ℤ`-graded commutative Hopf algebra over a field
is unipotent, then the Hopf algebra has graded matrix coefficients forming an upper
unitriangular matrix. -/
theorem exists_unitriangular_of_isUnipotent {k : Type u} [Field k]
    (A : CommHopfAlgCat.{u} (CommRingCat.of k)) (𝒜 : ℤ → Submodule k A) [GradedAlgebra 𝒜]
    (h𝒜 : IsGradedBialgebra 𝒜) [Algebra.FiniteType k A]
    (hU : IsUnipotent ((hopfSpec (CommRingCat.of k)).obj (op A))) :
    ∃ G : GradedMatrixCoefficients 𝒜, (∀ i, G.M i i = 1) ∧ ∀ i j, j < i → G.M i j = 0 := by
  classical
  have hfix : ∀ (m : ℕ) (b : Matrix (Fin (m + 1)) (Fin (m + 1)) A), Triangular.IsCorep k b →
      ∃ v : Fin (m + 1) → k, v ≠ 0 ∧ ∀ i, ∑ j, v j • b i j = v i • (1 : A) := by
    intro m b hb
    rw [Triangular.isCorep_iff] at hb
    exact UnipotentMatrixCriterion.exists_fixedVector_of_isUnipotent A hU b hb.1
      fun i j => by rw [hb.2, Matrix.one_apply]
  obtain ⟨n, w, a, ha, hg, hadj⟩ := GradedComodule.exists_corep_adjoin_eq_top h𝒜
  obtain ⟨w', P, Q, hPQ, hP, hT⟩ := Triangular.exists_unitriangular_conj 𝒜 hfix n w a ha hg
  have hc := (Triangular.isCorep_iff _).1 (ha.conj hPQ)
  exact ⟨{ n := n
           w := w'
           M := Triangular.conj Q P a
           comul_apply := hc.1
           counit_apply := hc.2
           mem := hg.conj hP (hP.of_mul_eq_one hPQ (mul_eq_one_comm.1 hPQ))
           adjoin_eq_top := Triangular.adjoin_conj hPQ hadj }, hT.1, hT.2⟩

/-- `exists_unitriangular_of_isUnipotent`, stated with `GradedMatrixCoefficients.IsUnitriangular`. -/
theorem exists_isUnitriangular_of_isUnipotent {k : Type u} [Field k]
    (A : CommHopfAlgCat.{u} (CommRingCat.of k)) (𝒜 : ℤ → Submodule k A) [GradedAlgebra 𝒜]
    (h𝒜 : IsGradedBialgebra 𝒜) [Algebra.FiniteType k A]
    (hU : IsUnipotent ((hopfSpec (CommRingCat.of k)).obj (op A))) :
    ∃ G : GradedMatrixCoefficients 𝒜, G.IsUnitriangular :=
  exists_unitriangular_of_isUnipotent A 𝒜 h𝒜 hU

end Langlands.Algebra.GradedHopf
