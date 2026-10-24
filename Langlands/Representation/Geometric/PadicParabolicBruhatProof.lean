import Langlands.Representation.Geometric.BruhatDescent
import Langlands.Representation.Geometric.BruhatMatrixExistenceProof
import Langlands.Representation.Geometric.BruhatWeylReflectionProof
import Langlands.Representation.Geometric.WeylMinimalRepresentativeProof

namespace Langlands.Geometric

open GeneralLinear

universe u

/-- Weyl bijectivity, matrix representatives, and reflection assemble to
bijectivity of the actual inverse permutation-matrix map. -/
theorem parabolicDoubleCoset_bijective_of_matrix_conditions
    (R : Type u) [CommRing R] {n : ℕ} (B C : BlockShape n)
    (hW : Function.Bijective (weylDoubleCoset B C))
    (hE : ∀ g : GeneralLinear n R, ∃ w : Equiv.Perm (Fin n),
      DoubleCoset.mk (B.parabolic R) (C.parabolic R) (permutation n R w)⁻¹ =
        DoubleCoset.mk (B.parabolic R) (C.parabolic R) g)
    (hR : ∀ v w : Equiv.Perm (Fin n),
      DoubleCoset.mk (B.parabolic R) (C.parabolic R) (permutation n R v)⁻¹ =
        DoubleCoset.mk (B.parabolic R) (C.parabolic R) (permutation n R w)⁻¹ →
      DoubleCoset.mk (blockWeyl C) (blockWeyl B) v =
        DoubleCoset.mk (blockWeyl C) (blockWeyl B) w) :
    Function.Bijective (parabolicDoubleCoset R B C) := by
  constructor
  · intro v w h
    apply hW.1
    exact hR v.val w.val h
  · intro q
    obtain ⟨g, rfl⟩ := Quotient.exists_rep q
    obtain ⟨w, hw⟩ := hE g
    obtain ⟨v, hv⟩ := hW.2 (DoubleCoset.mk (blockWeyl C) (blockWeyl B) w)
    refine ⟨v, ?_⟩
    exact (congrArg (weylToParabolicDoubleCoset R B C) hv).trans hw

/-- Minimal permutations parametrize the actual p-adic parabolic double cosets
by their inverse permutation matrices. -/
theorem padicParabolicBruhat : PadicParabolicBruhatTheorem.{u} := by
  intro p hp F n hn B C
  exact parabolicDoubleCoset_bijective_of_matrix_conditions F.Carrier B C
    (weylMinimalRepresentativeTheorem n hn B C)
    (padicBruhatMatrixExistence p F n hn B C)
    (padicBruhatWeylReflection p F n hn B C)

end Langlands.Geometric
