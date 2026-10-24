import Langlands.Representation.Geometric.BruhatMatrixStatement
import Langlands.Group.GL.TriangularParabolic
import Langlands.Group.GL.UpperBruhatProof

namespace Langlands.Geometric

open GeneralLinear

universe u

/-- A concrete triangular factorization gives the required inverse-permutation class. -/
theorem inverse_permutation_doubleCoset_of_upper_factorization
    {R : Type u} [CommRing R] {n : ℕ} (B C : BlockShape n)
    (g a b : GeneralLinear n R) (w : Equiv.Perm (Fin n))
    (ha : ∀ i j : Fin n, j < i → a i j = 0)
    (hb : ∀ i j : Fin n, j < i → b i j = 0)
    (hg : g = a * permutation n R w * b) :
    DoubleCoset.mk (B.parabolic R) (C.parabolic R)
        (permutation n R w⁻¹)⁻¹ =
      DoubleCoset.mk (B.parabolic R) (C.parabolic R) g := by
  apply DoubleCoset.eq.mpr
  refine ⟨a, B.mem_parabolic_of_isUpperTriangular a (fun {i j} hij => ha i j hij),
    b, C.mem_parabolic_of_isUpperTriangular b (fun {i j} hij => hb i j hij), ?_⟩
  simpa only [permutation_inv, inv_inv] using hg

/-- Every p-adic parabolic double coset has an inverse permutation-matrix representative. -/
theorem padicBruhatMatrixExistence : PadicBruhatMatrixExistenceTheorem.{u} := by
  intro p hp F n _ B C g
  obtain ⟨a, b, w, ha, hb, hg⟩ := fieldUpperBruhatFactorizationTheorem F.Carrier n g
  exact ⟨w⁻¹, inverse_permutation_doubleCoset_of_upper_factorization B C g a b w ha hb hg⟩

end Langlands.Geometric
