/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 56, 13 November 2026:
Extract only the asserted type of M288.001
AmbientEmbeddedFixedFieldPresentation.quotientRestriction from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/
FixedFieldIntrinsicReciprocity/NormRestriction.lean at
fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL namespace
prefix and package all forty-five original binders inside a closed
Prop-valued definition with the suffix Statement, preserving their order,
binder kinds and the source's universe-zero field types. The seven
instance-implicit hypotheses become anonymous instance binders and the two
compatibility hypotheses hbase and hcompat, which the conclusion does not
mention, become unnamed implication premises in their source positions.
Open only the published namespaces of extensionSubgroup and of the class
formation declarations, keep the scoped IsMulCommutative opening, and
replace the source imports by the published modules defining the ambient
presentation, the abelianized restriction and le_baseField, with Mathlib's
abelianization and abelian Galois modules. Defer the truth proof; install
no instance or simp registration. Omit the original noncomputable section
and all other declarations of the module.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.FieldTheory.Galois.Abelian
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.U005.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Main.U019.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.AmbientNormResidue.U002.Definitions

/-!
# Restriction of embedded Galois actions on ambient quotient representatives: statement

A closed proposition saying that a restriction homomorphism between two
finite abelian Galois groups of local field extensions, compatible with
their embeddings into the separable closure, agrees with the abelianized
restriction between the corresponding ambient finite Galois quotients.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open Langlands.NYLL.CyclicCohomology Langlands.NYLL.ClassFormation
open scoped IsMulCommutative

/-- A compatible restriction of concrete embedded Galois actions induces the
corresponding restriction map on ambient finite quotient representatives. -/
def AmbientEmbeddedFixedFieldPresentation.quotientRestrictionStatement :
    Prop :=
  ∀ (K K' L L' : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field K'] [ValuativeRel K'] [TopologicalSpace K']
    [IsNonarchimedeanLocalField K']
    [Field L] [Field L']
    [Algebra K K'] [Algebra K L] [Algebra K L']
    [Algebra K' L'] [Algebra L L']
    [IsScalarTower K K' L'] [IsScalarTower K L L']
    [FiniteDimensional K K'] [Algebra.IsSeparable K K']
    [Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation K')]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [FiniteDimensional K' L'] [IsAbelianGalois K' L']
    {jLower : L →ₐ[K] SeparableClosure K}
    {jUpper : L' →ₐ[K] SeparableClosure K}
    (lower : AmbientEmbeddedFixedFieldPresentation K K L jLower)
    (upper : AmbientEmbeddedFixedFieldPresentation K K' L' jUpper)
    (hH'H : upper.base.field.toSubgroup ≤ lower.base.field.toSubgroup)
    (hJ'J : upper.extension.field.toSubgroup ≤
      lower.extension.field.toSubgroup)
    [(extensionSubgroup lower.base.field lower.extension.field
        lower.extension.below).Normal]
    [Finite
      (lower.base.field.toSubgroup ⧸
        extensionSubgroup lower.base.field lower.extension.field
          lower.extension.below)]
    [(extensionSubgroup upper.base.field upper.extension.field
        upper.extension.below).Normal]
    [Finite
      (upper.base.field.toSubgroup ⧸
        extensionSubgroup upper.base.field upper.extension.field
          upper.extension.below)]
    [Finite
      ((baseField Gal(SeparableClosure K/K)).toSubgroup ⧸
        extensionSubgroup
          (baseField Gal(SeparableClosure K/K))
          lower.base.field (le_baseField lower.base.field))]
    [Finite
      ((baseField Gal(SeparableClosure K/K)).toSubgroup ⧸
        extensionSubgroup
          (baseField Gal(SeparableClosure K/K))
          upper.base.field (le_baseField upper.base.field))]
    [Finite
      (lower.base.field.toSubgroup ⧸
        extensionSubgroup lower.base.field upper.base.field hH'H)]
    (restrictActual : Gal(L'/K') →* Gal(L/K)),
    (∀ x : L, jUpper (algebraMap L L' x) = jLower x) →
      (∀ (τ : Gal(L' / K')) (x : L),
        jLower (restrictActual τ x) =
          jUpper (τ (algebraMap L L' x))) →
        ∀ (z : Abelianization
          (upper.base.field.toSubgroup ⧸
            extensionSubgroup upper.base.field upper.extension.field
              upper.extension.below)),
          restrictActual
              ((Abelianization.equivOfComm (H := Gal(L' / K'))).symm
                ((upper.extension.extensionQuotientMulEquiv.symm.trans
                  upper.quotientEquiv).abelianizationCongr z)) =
            (Abelianization.equivOfComm (H := Gal(L / K))).symm
              ((lower.extension.extensionQuotientMulEquiv.symm.trans
                lower.quotientEquiv).abelianizationCongr
                (normResidueNaturalityAbelianizedRestriction
                  lower.base.field upper.base.field
                  lower.extension.field upper.extension.field
                  lower.extension.below upper.extension.below
                  hH'H hJ'J z))

end Langlands.NYLL.LocalClassFieldTheory
