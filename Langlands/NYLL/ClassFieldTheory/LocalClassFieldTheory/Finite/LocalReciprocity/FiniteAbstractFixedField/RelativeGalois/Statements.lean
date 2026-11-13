/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField.Initial.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField.Relative.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.U005.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteExtension.Definitions
import Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions

/-!
# Relative abstract fixed fields: Galois, finiteness and degree targets

Adapted by Worker 4913 from NYLL commit
`fbd320cd8b1b06487c58227e92eb135794267709`, units M099.012, M099.019 and
M099.020 of
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteAbstractFixedField.lean`.
The three source theorems become Prop-valued definitions with the suffix
`Statement`; their proofs are omitted. The source section variables are
written as explicit binders of each definition, so that `[IsGalois k Ω]` is
retained exactly as in the source theorems. The namespace is prefixed with
`Langlands.NYLL`, the source imports are replaced by the published modules
supplying the used declarations, and the unused `open RamificationTheory
KummerTheory` is omitted. The M099.019 docstring drops its opening word
"same", which refers to a source theorem not in this file. See the paired
Markdown for the declaration map and complete modification record. The
original license and notices are retained in `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory
open CyclicCohomology ClassFormation

noncomputable section

/-- The concrete relative fixed field is Galois precisely from the normality
witness occurring in the abstract cyclic extension. -/
def abstractRelativeFixedField_isGaloisStatement
    (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
    (K L : ClosedSubgroup (Gal(Ω/k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal) : Prop :=
  IsGalois (abstractFixedField k Ω K)
    (abstractRelativeFixedField k Ω hLK)

/-- The relative finiteness statement in the scalar-extended
intermediate-field presentation used by infinite Galois theory. -/
def abstractRelativeFixedField_finiteDimensionalStatement
    (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
    (K L : ClosedSubgroup (Gal(Ω/k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hKfinite : Finite ((baseField (Gal(Ω/k))).toSubgroup ⧸
      extensionSubgroup (baseField (Gal(Ω/k))) K (le_baseField K)))
    (hLKfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)) : Prop :=
  FiniteDimensional (abstractFixedField k Ω K)
    (abstractRelativeFixedField k Ω hLK)

/-- The abstract extension degree is the ordinary degree of the concrete
finite Galois extension represented by the same pair of fixed fields. -/
def finiteAbstractExtension_degree_eq_finrankStatement
    (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
    (K L : ClosedSubgroup (Gal(Ω/k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    (hKfinite : Finite ((baseField (Gal(Ω/k))).toSubgroup ⧸
      extensionSubgroup (baseField (Gal(Ω/k))) K (le_baseField K)))
    (hLKfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)) : Prop :=
  ((DegreeData.FiniteAbstractExtension.ofInclusion L K hLK).degree : ℕ) =
    Module.finrank (abstractFixedField k Ω K)
      (abstractRelativeFixedField k Ω hLK)

end
end Langlands.NYLL.LocalClassFieldTheory
