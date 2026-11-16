/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 546, 14–16 November 2026: extract the type of M402.002
(OrderReversal.lean, lines 64–71) from upstream commit
fbd320cd8b1b06487c58227e92eb135794267709; prefix the namespace with
Langlands.NYLL and universally close the complete theorem telescope as a
Prop-valued definition with a Statement suffix. Omit the source proof
(lines 72–81), replace broad imports by focused dependency modules, and
remove unused namespace openings. See the paired Markdown for details.
The original LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Mathlib.FieldTheory.Galois.Abelian
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianSubextension.NormSubgroup.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.OrderReversal.U001.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntrinsicAbsoluteData.Initial.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableUnitsNorm.BaseUnits.Definitions
import Langlands.NYLL.GaloisCohomology.Cyclic.TateH0.NormImage.Definitions

/-!
# Embedded finite-abelian norm transport: proposition target

Source: M402.002, lines 64–71 of
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/OrderReversal.lean`.
-/

noncomputable section

namespace Langlands.NYLL.LocalClassFieldTheory

open CyclicCohomology

/-- Under the canonical identification of the abstract base fixed units with
`Kˣ`, the abstract norm subgroup of an embedded finite abelian extension is
its ordinary field-norm subgroup. -/
def map_finiteAbelianAbstractExtension_normSubgroup_eqStatement : Prop :=
  ∀ (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    (i : L →ₐ[K] SeparableClosure K),
    ((finiteAbelianAbstractExtensionOfEmbedding K L i).normSubgroup
        (intrinsicAbsoluteUnits K)).map
      (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm.toAddMonoidHom =
      additiveNormSubgroup K L

end Langlands.NYLL.LocalClassFieldTheory

end
