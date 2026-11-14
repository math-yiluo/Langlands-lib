/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 56, 14 November 2026:
Extract only M282.003 from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/
FixedFieldIntrinsicReciprocity/AmbientNormResidue.lean at
fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL namespace
prefix and keep the docstring, binders and body. Replace the source imports
by the published modules defining the ambient fixed-field presentation and
the quotient/Galois equivalence of abstract fixed fields; no namespace is
opened, since the definition names nothing outside its own namespace except
through dot notation. Omit all other declarations of the module.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.AmbientNormResidue.U002.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField.Equivalences.Definitions

/-!
# The fixed-field quotient equivalence of an ambient presentation

For an ambient fixed-field presentation of an embedded finite Galois
extension, the canonical isomorphism from the finite quotient of the ambient
closed subgroups to the Galois group of the corresponding concrete relative
fixed field.
-/

noncomputable section

namespace Langlands.NYLL.LocalClassFieldTheory

namespace AmbientEmbeddedFixedFieldPresentation

/-- The canonical quotient equivalence from an ambient finite fixed-field
extension to the Galois group of its relative fixed field. -/
noncomputable def fixedFieldQuotientEquiv
    {K F E : Type}
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field E] [Algebra K F] [Algebra F E] [Algebra K E]
    [IsScalarTower K F E]
    [FiniteDimensional K F] [Algebra.IsSeparable K F]
    [Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation F)]
    [FiniteDimensional F E] [IsGalois F E]
    {j : E →ₐ[K] SeparableClosure K}
    (P : AmbientEmbeddedFixedFieldPresentation K F E j) :
    P.extension.extensionQuotient ≃*
      Gal(abstractRelativeFixedField K (SeparableClosure K)
        P.extension.below /
        abstractFixedField K (SeparableClosure K) P.base.field) :=
  P.extension.extensionQuotientMulEquiv.trans
    (abstractExtensionQuotientEquivGaloisGroup
      K (SeparableClosure K) P.base.field P.extension.field
      P.extension.below P.extension.normal)

end AmbientEmbeddedFixedFieldPresentation

end Langlands.NYLL.LocalClassFieldTheory

end
