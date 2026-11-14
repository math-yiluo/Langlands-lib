/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 57, 14 November 2026:
Extract the statement of M098.027 from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/
ConcreteReciprocityCanonical.lean at
fbd320cd8b1b06487c58227e92eb135794267709 as a closed Prop-valued definition
without its proof. The section variables used become universal binders in
the same order. The private abbreviation B K of the source is unfolded to
intrinsicAbstractBase K. Add the Langlands.NYLL namespace prefix and the
suffix Statement. Import the Library modules that publish
finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding (M090.009) and
intrinsicAbstractBase (M091.003) instead of the source imports. Omit the
noncomputable section, the three open lines, which this statement does not
use, the simp attribute, and all other declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteGaloisRealization.Quotient.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntrinsicAbsoluteData.Initial.Definitions

/-!
# Finite Galois realization: the quotient equivalence on representatives

A closed proposition computing the published equivalence
`finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L i` on the class
of an element `τ` of the intrinsic base subgroup: after applying the
embedding `i`, the resulting automorphism of `L` acts as `τ` does on `i(L)`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

/-- Formula for the quotient equivalence on a representative, expressed
without mentioning the auxiliary fixed-field equality used internally. -/
def finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding_mk_applyStatement :
    Prop :=
  ∀ (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (i : L →ₐ[K] SeparableClosure K)
    (τ : (intrinsicAbstractBase K).toSubgroup) (x : L),
    i ((finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L i
      (QuotientGroup.mk τ)) x) = τ.1 (i x)

end Langlands.NYLL.LocalClassFieldTheory
