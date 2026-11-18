import Langlands.AbelianScheme.EndomorphismDegreeLinePolynomialStatement
import Langlands.AbelianScheme.EndomorphismEulerDegree

/-! # Proof that degrees of endomorphisms are polynomial along lines -/

universe u

namespace Langlands.AbelianScheme

/-- `EndomorphismDegreeLinePolynomialStatement` holds, with `δ` the Euler-coefficient degree. -/
theorem endomorphismDegreeLinePolynomial : EndomorphismDegreeLinePolynomialStatement.{u} :=
  fun _ _ _ A g hg =>
    ⟨EndomorphismEulerDegree.endomorphismEulerDegree A g,
      EndomorphismEulerDegree.endomorphismEulerDegree_spec hg⟩

end Langlands.AbelianScheme
