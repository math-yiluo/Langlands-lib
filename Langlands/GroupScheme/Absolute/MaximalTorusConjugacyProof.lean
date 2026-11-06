import Langlands.GroupScheme.Absolute.BorelMaximalTorusReduction
import Langlands.GroupScheme.Absolute.BorelConjugacyProof
import Langlands.GroupScheme.Rational.SolvableMaximalTorusConjugacyProof

/-! # Conjugacy of maximal tori over algebraically closed fields -/

universe u

namespace Langlands.GroupScheme

/-- Any two maximal torus embeddings in a smooth connected affine group over an
algebraically closed field are conjugate by a rational point, with an isomorphism
of their sources as commutative group schemes. -/
theorem maximalTorusConjugacy : MaximalTorusConjugacyStatement.{u} :=
  maximalTorusConjugacyStatement_of_borelConjugacy
    borelConjugacy (fun k _ _ B _ _ _ hB => solvableMaximalTorusConjugacy k B hB)

end Langlands.GroupScheme
