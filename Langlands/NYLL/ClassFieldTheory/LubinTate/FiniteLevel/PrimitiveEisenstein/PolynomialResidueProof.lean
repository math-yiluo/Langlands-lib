/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 194, 2026-11-16: extract M340.001 (lines 44–52)
from upstream commit fbd320cd8b1b06487c58227e92eb135794267709;
prefix the namespace with Langlands.NYLL, import the published target and
uniformizer-residue proof, state the theorem as the fully applied target,
and make the residue equality and simplification rules explicit. Replace the
module documentation and omit unused section/scoped commands.
The retained license and notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveEisenstein.ResidueStatements
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.CoefficientEquation.U001.Proofs

/-!
# Residue reduction of the standard Lubin--Tate polynomial

Exact proof of NYLL M340.001 against its published target.
-/

universe u v

namespace Langlands.NYLL.LubinTate

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

/-- Reduction modulo the maximal ideal sends the standard Lubin--Tate
polynomial to `X ^ q`. -/
theorem standardLubinTatePolynomial_map_residue
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) :
    standardLubinTatePolynomial_map_residueStatement hπ := by
  have hzero : F.residueMap π = 0 :=
    SameUniformizer.residueMap_uniformizer_eq_zero hπ
  simp only [standardLubinTatePolynomial_map_residueStatement,
    standardLubinTatePolynomial, Polynomial.map_add, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.map_mul, Polynomial.map_C, hzero,
    Polynomial.C_0, zero_mul, add_zero]

end Langlands.NYLL.LubinTate
