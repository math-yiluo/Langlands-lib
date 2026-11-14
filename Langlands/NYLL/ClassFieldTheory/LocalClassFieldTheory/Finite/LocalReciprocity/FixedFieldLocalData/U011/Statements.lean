/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 57, 14 November 2026:
Extract the statement of M272.011 from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/
FixedFieldLocalData.lean
at fbd320cd8b1b06487c58227e92eb135794267709 as a closed Prop-valued
definition without its proof. Add the Langlands.NYLL namespace prefix and the
suffix Statement. Unfold the private abbreviation finiteFixedField K H to
abstractFixedField K (SeparableClosure K) H.field, and supply the source's
local instance finiteFixedFieldSeparableClosureAlgebra by a letI with the
same body before the binder that uses it. Replace the source's spectral norm,
valuative relation and local-field instance (M270.003, M270.007, M270.008) by
the Library's Langlands.LocalField.FiniteExtension.normedField, valuativeRel
and isLocalField. Import the Library modules that publish the declarations
used instead of the source imports. Omit the noncomputable section, the open
lines this statement does not need, the open ... in line used only by the
proof, and all other declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.LocalField.FiniteExtension
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteAbstractField.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField.Finiteness.U005.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.LocalResidueDatum.U006.Definitions

/-!
# The chosen valuation rings on a finite fixed field: statement

A closed proposition about a nonarchimedean local field `K` and an abstract
field `H` finite over the base in `Gal(SeparableClosure K / K)`. Its fixed
field `F` in `SeparableClosure K` is a finite extension of `K`, given its
spectral local-field structure. Every `F`-algebra equivalence
`e : SeparableClosure F ≃ₐ[F] SeparableClosure K` identifies the chosen
valuation rings `localSeparableValuationSubring F` and
`localSeparableValuationSubring K`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open ClassFormation

/-- Every `F`-algebra equivalence from the standard separable closure of a
finite fixed field `F` to the original ambient separable closure identifies
the two uniquely extended local valuation rings. -/
def localSeparableValuationSubring_eq_comap_abstractFixedFieldEquivStatement :
    Prop :=
  ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (H : FiniteAbstractField (Gal(SeparableClosure K / K))),
    letI : Algebra (abstractFixedField K (SeparableClosure K) H.field)
        (SeparableClosure (abstractFixedField K (SeparableClosure K) H.field)) :=
      (separableClosure (abstractFixedField K (SeparableClosure K) H.field)
        (AlgebraicClosure
          (abstractFixedField K (SeparableClosure K) H.field))).algebra
    ∀ (e : SeparableClosure (abstractFixedField K (SeparableClosure K) H.field) ≃ₐ[
          abstractFixedField K (SeparableClosure K) H.field] SeparableClosure K),
    letI : FiniteDimensional K
        (abstractFixedField K (SeparableClosure K) H.field) :=
      abstractFixedField_finiteDimensional
        K (SeparableClosure K) H.field H.finite
    letI : NontriviallyNormedField
        (abstractFixedField K (SeparableClosure K) H.field) :=
      Langlands.LocalField.FiniteExtension.normedField K
        (abstractFixedField K (SeparableClosure K) H.field)
    letI : ValuativeRel
        (abstractFixedField K (SeparableClosure K) H.field) :=
      Langlands.LocalField.FiniteExtension.valuativeRel K
        (abstractFixedField K (SeparableClosure K) H.field)
    letI : IsNonarchimedeanLocalField
        (abstractFixedField K (SeparableClosure K) H.field) :=
      Langlands.LocalField.FiniteExtension.isLocalField K
        (abstractFixedField K (SeparableClosure K) H.field)
    localSeparableValuationSubring
        (abstractFixedField K (SeparableClosure K) H.field) =
      (localSeparableValuationSubring K).comap e.toRingHom

end Langlands.NYLL.LocalClassFieldTheory
