import Langlands.Global.Factors.CuspidalFinitePairRegularityStatement
import Langlands.Representation.RankinSelberg.UnitaryGenericLPolynomialNonvanishingStatement
import Langlands.Representation.RankinSelberg.UnitaryGenericLPolynomialNonvanishingProof
import Langlands.Representation.RankinSelberg.GenericLanglandsQuotientLFactorProof
import Langlands.Correspondence.AutomorphicPairFactors
import Langlands.Automorphic.CuspidalUnitaryLocalGenericity
import Langlands.Automorphic.CuspidalUnitaryLocalUnitarityProof

/-!
# Regularity of the finite pair L-factors of unitary cuspidal realizations on `Re s ≥ 1`

Proof of `CuspidalFinitePairRegularityStatement` (Getz–Hahn, Theorem 11.5.2, non-Archimedean
case, for the finite local components of two unitary cuspidal realizations).

* `cuspidalFinitePairRegularity_of_unitaryGeneric` reduces the target to the local p-adic
  statement `RankinSelberg.UnitaryGenericLPolynomialNonvanishingStatement` (Getz–Hahn
  Theorem 11.5.2, p-adic case, for the JPSS polynomial of generic unitarizable
  representations): the local components of unitary cuspidal realizations are generic and
  unitarizable, and the L-polynomial of the finite pair data, defined through standard modules,
  is the JPSS polynomial of the components (JPSS (9.4)(4), proved as
  `RankinSelberg.genericLanglandsQuotientLFactor`).
* `cuspidalFinitePairRegularity` applies the reduction to the proof
  `RankinSelberg.UnitaryGeneric.unitaryGenericLPolynomialNonvanishing` of the local statement.
-/

noncomputable section

set_option autoImplicit false

universe u uQ

namespace Langlands.Global

open NumberField
open Langlands.Global.CompletionPadic
open Automorphic (CuspidalOperatorRealization CuspidalSpectralPresentation)
open CuspidalPairFunctionalEquation (HasIrreducibleAdmissibleComponents residueCardinality)

/-- **Finite pair regularity from the local statement.** The local p-adic statement
`UnitaryGenericLPolynomialNonvanishingStatement`, with all three universes equal to `u`,
implies `CuspidalFinitePairRegularityStatement`. -/
theorem cuspidalFinitePairRegularity_of_unitaryGeneric
    (h6387 : RankinSelberg.UnitaryGenericLPolynomialNonvanishingStatement.{u, u, u}) :
    CuspidalFinitePairRegularityStatement.{u, uQ} := by
  intro F _ _ _ r t T T' hT hT' P P' h h' c v s hs
  have hspec := c.lPolynomial_spec v
  have hL := (Correspondence.isAutomorphicPairLPolynomial_iff (padicField v)
    ((P.localComponent v).padicObject (h v).1 (h v).2)
    ((P'.localComponent v).padicObject (h' v).1 (h' v).2)
    ((P.localComponent v).padicObject (h v).1 (h v).2).obj
    ((P'.localComponent v).padicObject (h' v).1 (h' v).2).obj
    (Representation.Equiv.refl _) (Representation.Equiv.refl _)).mp hspec
  obtain ⟨⟨d, hd⟩, ⟨e, he⟩, hall⟩ := hL
  have hgen := Automorphic.cuspidalUnitaryLocalGenericity F r T hT P v (h v).1 (h v).2
    (c.additive v)
  have hgen' := Automorphic.cuspidalUnitaryLocalGenericity F t T' hT' P' v (h' v).1 (h' v).2
    (c.additive v)
  have hunit := Automorphic.cuspidalUnitaryLocalUnitarity F r T hT P v (h v).1 (h v).2
  have hunit' := Automorphic.cuspidalUnitaryLocalUnitarity F t T' hT' P' v (h' v).1 (h' v).2
  let ν : LocalFactor.PadicAbelian.SelfDualHaar (padicField v).canonicalTopologicalData
      (c.additive v) := ⟨c.measure v, c.measure_spec v⟩
  obtain ⟨P₀, hP₀std, hP₀⟩ := RankinSelberg.genericLanglandsQuotientLFactor (residuePrime v)
    (padicField v) (c.additive v) ν r t d e
    ((P.localComponent v).padicObject (h v).1 (h v).2).obj
    ((P'.localComponent v).padicObject (h' v).1 (h' v).2).obj hd he hgen hgen'
  have hEq : c.lPolynomial v = P₀ := (hall d e hd he).unique hP₀std
  rw [hEq]
  exact h6387 (residuePrime v) (padicField v) (c.additive v) ν r t _ _ hgen hunit hgen' hunit'
    P₀ hP₀ s hs

/-- **Regularity of the finite pair L-factors of unitary cuspidal realizations on
`Re(s) ≥ 1`** (Getz–Hahn Theorem 11.5.2, non-Archimedean case, in the normalization of the
finite pair L-data of the pole statement). -/
theorem cuspidalFinitePairRegularity : CuspidalFinitePairRegularityStatement.{u, uQ} :=
  cuspidalFinitePairRegularity_of_unitaryGeneric
    RankinSelberg.UnitaryGeneric.unitaryGenericLPolynomialNonvanishing.{u, u, u}

end Langlands.Global
