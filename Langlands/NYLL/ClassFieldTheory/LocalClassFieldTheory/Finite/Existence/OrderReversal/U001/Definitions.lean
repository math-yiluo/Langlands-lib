/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.FieldTheory.Galois.Abelian
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianSubextension.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ConcreteReciprocityTransport.Extension.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteGaloisRealization.Quotient.Definitions

/-!
# An embedded finite abelian extension as an abstract subextension

Adapted by Worker 543 from NYLL commit
`fbd320cd8b1b06487c58227e92eb135794267709`, unit M402.001, lines 35–59 of
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/OrderReversal.lean`.
This focused extraction prefixes the namespace with `Langlands.NYLL`, uses
published dependency modules, and omits unused namespace opens. The definition,
explicit Type-0 parameters, instances, docstring and body are unchanged.
See the paired Markdown for the exact declaration map and modifications.
The original license and notices are retained in `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

noncomputable section

namespace Langlands.NYLL.LocalClassFieldTheory

open RamificationTheory CyclicCohomology ClassFormation

/-- A finite abelian extension, realized by an explicit embedding in the
fixed separable closure, as an abstract finite abelian subextension. -/
def finiteAbelianAbstractExtensionOfEmbedding
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    (i : L →ₐ[K] SeparableClosure K) :
    FiniteAbelianSubextension (intrinsicAbstractBase K) where
  toFiniteGaloisExtension :=
    finiteGaloisAbstractExtensionOfEmbedding K L i
  commutative := by
    change IsMulCommutative
      ((closedFixingSubgroup K (SeparableClosure K)
          (⊥ : IntermediateField K (SeparableClosure K))).toSubgroup ⧸
        extensionSubgroup
          (closedFixingSubgroup K (SeparableClosure K)
            (⊥ : IntermediateField K (SeparableClosure K)))
          (finiteGaloisClosedFixingSubgroupOfEmbedding K L i)
          (fixingSubgroupLeBase K (SeparableClosure K)
            (finiteGaloisFieldRangeOfEmbedding K L i)))
    let e := finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L i
    exact
      { is_comm.comm := fun x y => by
          apply e.injective
          simp only [map_mul]
          exact
            (inferInstance :
              IsMulCommutative (Gal(L / K))).is_comm.comm (e x) (e y) }

end Langlands.NYLL.LocalClassFieldTheory
