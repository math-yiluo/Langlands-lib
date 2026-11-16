/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 571, 2026-11-16: extract M340.003 (lines 71–83)
from upstream commit fbd320cd8b1b06487c58227e92eb135794267709; prefix
the namespace with Langlands.NYLL; import the published target and focused
prerequisite proofs; state the theorem as the fully applied target; unfold
the prerequisite targets through explicitly typed local equalities; replace the
module documentation. See the paired Markdown. The retained license and
notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveEisenstein.ResidueStatements
import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveEisenstein.IterateResidueProof
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.CoefficientEquation.U001.Proofs

/-!
# Residue reduction of the standard primitive division polynomial

Exact proof of NYLL M340.003 against its published target.
-/

noncomputable section

universe u v

namespace Langlands.NYLL.LubinTate

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

/-- Reduction modulo the maximal ideal sends the primitive quotient
polynomial to its leading monomial. -/
theorem standardLubinTatePrimitivePolynomial_map_residue
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    standardLubinTatePrimitivePolynomial_map_residueStatement hπ n := by
  have hiter :
      (standardLubinTatePolynomialIterate F π n).map F.residueMap =
        Polynomial.X ^ (Nat.card F.residueField ^ n) :=
    standardLubinTatePolynomialIterate_map_residue hπ n
  have hzero : F.residueMap π = 0 :=
    SameUniformizer.residueMap_uniformizer_eq_zero hπ
  simp [standardLubinTatePrimitivePolynomial_map_residueStatement,
    standardLubinTatePrimitivePolynomial, hiter, hzero,
    ← pow_mul, Nat.mul_comm]

end Langlands.NYLL.LubinTate

end
