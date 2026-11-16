/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 784, 2026-11-16: extract the proof of M340.002
from upstream commit fbd320cd8b1b06487c58227e92eb135794267709;
prefix the namespace with Langlands.NYLL, use the fully applied
published Statement as the theorem type, and replace the source imports
by the focused published statement and prerequisite proof modules.
Unfold the Statement wrappers explicitly for rewriting.
See the paired Markdown for the full adaptation record.
The retained license and notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveEisenstein.ResidueStatements
import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.DivisionPolynomial.Iterate.SuccProof
import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveEisenstein.PolynomialResidueProof

/-!
# Residue reduction of the standard Lubin--Tate polynomial iterates

The standard `n`-fold compositional iterate reduces to `X ^ (q ^ n)`,
where `q` is the residue-field cardinality.
-/

noncomputable section

universe u v

namespace Langlands.NYLL.LubinTate

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

/-- Reduction modulo the maximal ideal sends the `n`-fold standard iterate
to `X ^ (q ^ n)`. -/
theorem standardLubinTatePolynomialIterate_map_residue
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    standardLubinTatePolynomialIterate_map_residueStatement hπ n := by
  unfold standardLubinTatePolynomialIterate_map_residueStatement
  induction n with
  | zero =>
      simp [standardLubinTatePolynomialIterate]
  | succ n ih =>
      have hsucc :
          standardLubinTatePolynomialIterate F π (n + 1) =
            (standardLubinTatePolynomial F π).comp
              (standardLubinTatePolynomialIterate F π n) := by
        exact standardLubinTatePolynomialIterate_succ F π n
      have hresidue :
          (standardLubinTatePolynomial F π).map F.residueMap =
            Polynomial.X ^ Nat.card F.residueField := by
        exact standardLubinTatePolynomial_map_residue hπ
      rw [hsucc, Polynomial.map_comp, hresidue, ih]
      simp [← pow_mul, pow_succ]

end Langlands.NYLL.LubinTate

end
