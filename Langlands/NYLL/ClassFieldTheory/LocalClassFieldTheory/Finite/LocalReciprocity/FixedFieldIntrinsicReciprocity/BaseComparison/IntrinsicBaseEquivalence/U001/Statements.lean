/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 57, 13 November 2026:
Extract the statement of M273.001 from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/
FixedFieldIntrinsicReciprocity/BaseComparison/IntrinsicBaseEquivalence.lean
at fbd320cd8b1b06487c58227e92eb135794267709 as a closed Prop-valued
definition without its proof. Add the Langlands.NYLL namespace prefix and the
suffix Statement. Write the source abbreviation
CyclicCohomology.extensionSubgroup (baseField _) H₀ (le_baseField H₀) as its
body H₀.toSubgroup.subgroupOf (baseField _).toSubgroup, which does not use the
inclusion proof. Qualify the published names closedFixingSubgroup and
baseField, and import their Library modules and Mathlib.FieldTheory.IsSepClosed
instead of the source imports. Omit all other declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.Definitions
import Langlands.NYLL.ValuedFieldTheory.Ramification.GaloisValuation.ClosedFixingSubgroup.Definitions
import Mathlib.FieldTheory.IsSepClosed

/-!
# Finite quotient for an embedded finite extension: statement

The closed proposition that the closed subgroup of `Gal(SeparableClosure K / K)`
fixing the image of a finite extension `F` of `K` has a finite left-coset
quotient inside the distinguished base field.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

/-- The fixing subgroup of the image of a finite extension embedded in
`SeparableClosure K` has finite index in the ambient base-field subgroup. -/
def ambientEmbeddedAbsoluteQuotientFiniteStatement : Prop :=
  ∀ (K F : Type) [Field K] [Field F]
    [Algebra K F] [FiniteDimensional K F]
    (i : F →ₐ[K] SeparableClosure K),
    let H₀ :=
      Langlands.NYLL.RamificationTheory.closedFixingSubgroup K (SeparableClosure K)
        (AlgHom.fieldRange i)
    Finite
      ((Langlands.NYLL.ClassFormation.baseField
          Gal(SeparableClosure K / K)).toSubgroup ⧸
        H₀.toSubgroup.subgroupOf
          (Langlands.NYLL.ClassFormation.baseField
            Gal(SeparableClosure K / K)).toSubgroup)

end Langlands.NYLL.LocalClassFieldTheory
