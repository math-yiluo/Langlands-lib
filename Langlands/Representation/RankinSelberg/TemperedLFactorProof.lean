import Langlands.Representation.RankinSelberg.TemperedLFactorProduct
import Langlands.Representation.RankinSelberg.SquareIntegrableWhittakerTypeOfGenericityProof
import Langlands.Representation.Classification.SquareIntegrableGenericityProof
import Langlands.Representation.RankinSelberg.SquareIntegrablePoleFreeProof

/-!
# L-factors of square-integrable block inductions

Closed square-integrable genericity supplies full Whittaker type for every
original block. The certified product construction, with closed block
pole-freeness, then proves JPSS Proposition 8.4.
-/

noncomputable section

namespace Langlands.RankinSelberg

open HarmonicAnalysis Whittaker Polynomial

universe uF uV uW

/-- The L-polynomial of two square-integrable block inductions is the
double product of their block-pair L-polynomials and has no zero in the
open unit disk. -/
theorem temperedLFactor : TemperedLFactorStatement.{uF,uV,uW} := by
  intro p _ F ψ ν r t k l m n hm hn V _ _ W _ _ π σ hiπ hsπ hiσ hsσ
  let := F.canonicalTopologicalData.topology
  have hπ (i : Fin k) :
      IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (π i) :=
    squareIntegrableWhittakerType_of_genericity.{uF,uV}
      F (Classification.squareIntegrableGenericity.{uF,uV}
        F F.canonicalTopologicalData) ψ (m i) (π i) (hiπ i) (hsπ i)
  have hσ (j : Fin l) :
      IsOfWhittakerType (n j) (standardCharacter ψ (n j)) (σ j) :=
    squareIntegrableWhittakerType_of_genericity.{uF,uW}
      F (Classification.squareIntegrableGenericity.{uF,uW}
        F F.canonicalTopologicalData) ψ (n j) (σ j) (hiσ j) (hsσ j)
  obtain ⟨d⟩ := TemperedLFactorProduct.nonempty_productLPolynomialData
    F ψ ν m n hm hn π σ squareIntegrablePoleFree hπ hσ hiπ hsπ hiσ hsσ
  exact ⟨d.inducedPolynomial, d.blockPolynomial, d.induced_spec,
    d.block_spec, d.product_eq, d.poleFree⟩

end Langlands.RankinSelberg
