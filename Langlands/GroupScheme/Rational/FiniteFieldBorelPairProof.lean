import Langlands.GroupScheme.Rational.FiniteFieldBorelPairStatement
import Langlands.GroupScheme.Rational.FiniteFieldBorelPairExistence
import Langlands.GroupScheme.Rational.FiniteFieldBorelPairConjugacy
import Langlands.GroupScheme.Rational.FiniteFieldBorelPairAssembly

/-! # Borel pairs over finite fields -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

open FiniteFieldBorelPair

/-- Every smooth connected affine group over a finite field has a Borel pair,
and all its Borel pairs are conjugate by rational points. -/
theorem finiteFieldBorelPair : FiniteFieldBorelPairStatement.{u} := by
  intro k _ _ G _ _ _
  let : Fintype k := Fintype.ofFinite k
  refine ⟨exists_borelPair k G, ?_⟩
  intro B B' b b' T T' j j' hb hj hjb hb' hj' hjb'
  obtain ⟨g, hg⟩ := geometricBorel_rationalConjugate k G B B' b b' hb hb'
  exact pair_conjugacy_of_borel_conjugator b b' j j' hj hjb hb'.1 hj' hjb' g hg

end Langlands.GroupScheme
