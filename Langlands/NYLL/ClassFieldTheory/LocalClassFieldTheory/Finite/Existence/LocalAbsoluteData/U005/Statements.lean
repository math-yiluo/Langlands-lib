/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 450, 14 November 2026:
Extract the statement of M299.005 (source lines 67-76) from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/LocalAbsoluteData.lean
at fbd320cd8b1b06487c58227e92eb135794267709 as a Prop-valued definition
without its proof (source lines 77-103). Add the Langlands.NYLL namespace
prefix and the suffix Statement. Replace the three source imports by
Mathlib.FieldTheory.IsSepClosed (SeparableClosure and its IsGalois instance)
and the published Library modules supplying abstractFixedField, baseField,
extensionSubgroup and le_baseField. Open only CyclicCohomology and
ClassFormation, the namespaces of the published extensionSubgroup,
baseField and le_baseField. Omit all other declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Mathlib.FieldTheory.IsSepClosed
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField.Initial.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.U005.Proofs
import Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions

/-!
# NYLL M299.005: base normality makes the abstract fixed field Galois (statement)

For a field `K : Type` and a closed subgroup `H` of the absolute Galois group
`Gal(SeparableClosure K/K)`, normality of `H` inside the distinguished base
fixing group `baseField (Gal(SeparableClosure K/K))` implies that the concrete
fixed field `abstractFixedField K (SeparableClosure K) H` is Galois over `K`.
This module gives the Prop-valued target only; the proof is a separate unit.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open CyclicCohomology ClassFormation

/-- Normality over the abstract base fixing group makes the represented
fixed field Galois over the concrete local base field. -/
def abstractFixedField_isGalois_of_base_normalStatement
    (K : Type) [Field K]
    (H : ClosedSubgroup (Gal(SeparableClosure K/K)))
    (hnormal :
      (extensionSubgroup
        (baseField (Gal(SeparableClosure K/K))) H
        (le_baseField H)).Normal) : Prop :=
  IsGalois K (abstractFixedField K (SeparableClosure K) H)

end Langlands.NYLL.LocalClassFieldTheory
