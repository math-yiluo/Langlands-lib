/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.FieldTheory.Galois.Basic

/-!
# Unit Tate cardinality data

Adapted by Worker 203 from NYLL commit
`fbd320cd8b1b06487c58227e92eb135794267709`.
See the paired Markdown for the declaration map and complete modification record.
The original license and notices are retained in `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory
noncomputable section
/-- Finite-cardinality data for the two actual unit Tate groups.  Bundling the
`H⁰` finiteness proof keeps `Nat.card` honest when the local-field
structure on the extension is constructed inside a theorem. -/
structure UnitsTateCardinalityData
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] where
  /-- Finiteness of the degree-zero Tate cohomology group of the unit representation. -/
  finiteH0 : Finite (tateCohomology (Rep.ofAlgebraAutOnUnits K L) 0)
  /-- The degree-zero unit Tate group has cardinality equal to the extension degree. -/
  cardH0 :
    letI := finiteH0
    Nat.card (tateCohomology (Rep.ofAlgebraAutOnUnits K L) 0) = Module.finrank K L
  /-- The degree-minus-one unit Tate group is trivial at the level of cardinality. -/
  cardHminusOne : Nat.card (tateCohomology (Rep.ofAlgebraAutOnUnits K L) (-1)) = 1
end
end Langlands.NYLL.LocalClassFieldTheory
