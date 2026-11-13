/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 3, 2026-11-13: extract only M249.001–M249.003 and M249.006,
lines 45–64 and 86–92 of
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/LocalResidueDatum.lean
at upstream commit fbd320cd8b1b06487c58227e92eb135794267709; rename the two
local instances M249.001/M249.002 and the private definition M249.003 to
Langlands.NYLL.PortInternal.M249.d001, d002 and d003, keeping the two
instances local; prefix the namespace of M249.006 with Langlands.NYLL; replace
the source imports by Mathlib's separable-closure module and the two published
modules that supply localCompleteDVF and the Chevalley extension theorem. The
parameters, result types and bodies are otherwise unchanged. The retained
license and notices are in licenses/NYLL/.
-/

import Mathlib.FieldTheory.IsSepClosed
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionCompleteDVF.Canonical
import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.ChevalleyExtension.U003.Proofs

/-!
# The chosen valuation ring of the separable closure of a local field

This module adapts M249.001–M249.003 and M249.006 of
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/LocalResidueDatum.lean`:
a Chevalley extension of the canonical valuation of a nonarchimedean local
field `K` to `AlgebraicClosure K`, and its pullback to `SeparableClosure K`.
-/

noncomputable section

namespace Langlands.NYLL.PortInternal.M249

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- M249.001 (source `localSeparableClosureAlgebra`, a local instance): the
inclusion of the separable closure into the algebraic closure as an algebra. -/
local instance d001 :
    Algebra (SeparableClosure K) (AlgebraicClosure K) :=
  (separableClosure K (AlgebraicClosure K)).val.toRingHom.toAlgebra

/-- M249.002 (source `localSeparableClosureScalarTower`, a local instance):
the tower `K → SeparableClosure K → AlgebraicClosure K`. -/
local instance d002 :
    IsScalarTower K (SeparableClosure K) (AlgebraicClosure K) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- M249.003 (source private `localAbsoluteValuationSubring`): a Chevalley
extension of the local valuation to the chosen algebraic closure.  This is the
valuation choice `w | v` made in the finite local reciprocity construction. -/
noncomputable def d003 :
    ValuationSubring (AlgebraicClosure K) :=
  Classical.choose
    (Langlands.NYLL.ValuationTheory.DiscreteValuationField.Valuation.exists_extension_valuationSubring
      (L := AlgebraicClosure K) (Langlands.NYLL.LocalFieldTheory.localCompleteDVF K).valuation)

end Langlands.NYLL.PortInternal.M249

namespace Langlands.NYLL.LocalClassFieldTheory

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

attribute [local instance] Langlands.NYLL.PortInternal.M249.d001

/-- The valuation ring on the separable closure used in finite local reciprocity.
We choose it
as the pullback of the auxiliary valuation ring on the algebraic closure. -/
noncomputable def localSeparableValuationSubring :
    ValuationSubring (SeparableClosure K) :=
  (Langlands.NYLL.PortInternal.M249.d003 K).comap
    (algebraMap (SeparableClosure K) (AlgebraicClosure K))

end Langlands.NYLL.LocalClassFieldTheory

end
