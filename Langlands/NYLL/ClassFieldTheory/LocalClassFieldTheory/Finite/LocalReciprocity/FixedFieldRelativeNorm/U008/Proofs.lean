/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 56, 14 November 2026:
Prove the published closed form of M276.008
relativeNorm_abstractFixedFieldUnit_eq_normUnits from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/
FixedFieldRelativeNorm.lean at fbd320cd8b1b06487c58227e92eb135794267709
under the source theorem name with the Langlands.NYLL namespace prefix.
Keep the original tactic proof, applied after introducing the binders of the
closed statement; its cited source declarations are the published
Langlands.NYLL ones. Make the published M164.001 Fintype instance, whose
body is that of the source's local instance M276.001, a local instance.
Replace the source imports by the published modules supplying the used
declarations.
Worker 537, 16 November 2026: reuse Worker 56's shared proof draft
for Task 7285, compare its body with the pinned original and check the exact
published target against the current Library. Keep the proof unchanged.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldRelativeNorm.U008.Statements
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldRelativeNorm.U006.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldRelativeNorm.U007.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableNormProduct.U003.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField.RelativeGalois.U019.Proofs

/-!
# Relative norms on actual fixed fields: proof
-/

noncomputable section

open scoped BigOperators

namespace Langlands.NYLL.LocalClassFieldTheory

open Langlands.NYLL.CyclicCohomology Langlands.NYLL.ClassFormation

attribute [local instance] Langlands.NYLL.PortInternal.M164.d001

/-- The class-formation relative norm on fixed coefficients is the ordinary
field norm between the two concrete fixed fields, without a normality
assumption on the intermediate extension. -/
theorem relativeNorm_abstractFixedFieldUnit_eq_normUnits :
    relativeNorm_abstractFixedFieldUnit_eq_normUnitsStatement := by
  intro k Ω _ _ _ _ _ K L hLK hfinite hKabsolute x
  let : FiniteDimensional (abstractFixedField k Ω K)
      (abstractRelativeFixedField k Ω hLK) :=
    abstractRelativeFixedField_finiteDimensional
      k Ω K L hLK hKabsolute hfinite
  let : Algebra.IsSeparable (abstractFixedField k Ω K)
      (abstractRelativeFixedField k Ω hLK) :=
    Algebra.isSeparable_tower_bot_of_isSeparable
      (abstractFixedField k Ω K)
      (abstractRelativeFixedField k Ω hLK) Ω
  apply Subtype.ext
  apply Additive.ext
  apply Units.ext
  let Q := K.toSubgroup ⧸ extensionSubgroup K L hLK
  let := Fintype.ofFinite Q
  change
    ((Additive.toMul
      (relativeNormValue (galoisAmbientUnitsRep k Ω)
        K L hLK
        (abstractRelativeFixedFieldUnitsEquivGaloisFixed
          k Ω K L hLK (Additive.ofMul x))) : Ωˣ) : Ω) = _
  rw [relativeNormValue]
  change
    (↑(Additive.toMul (∑ q : Q,
      relativeCosetAction (galoisAmbientUnitsRep k Ω)
        K L hLK
        (abstractRelativeFixedFieldUnitsEquivGaloisFixed
          k Ω K L hLK (Additive.ofMul x)) q) : Ωˣ) : Ω) = _
  change (Units.coeHom Ω) (∏ q : Q,
    Additive.toMul
      (relativeCosetAction (galoisAmbientUnitsRep k Ω)
        K L hLK
        (abstractRelativeFixedFieldUnitsEquivGaloisFixed
          k Ω K L hLK (Additive.ofMul x)) q)) = _
  rw [map_prod]
  change
    (∏ q : Q,
      ((Additive.toMul
        (relativeCosetAction (galoisAmbientUnitsRep k Ω)
          K L hLK
          (abstractRelativeFixedFieldUnitsEquivGaloisFixed
            k Ω K L hLK (Additive.ofMul x)) q) : Ωˣ) : Ω)) = _
  calc
    _ = ∏ σ : abstractRelativeFixedField k Ω hLK →ₐ[
        abstractFixedField k Ω K] Ω,
        σ (x : abstractRelativeFixedField k Ω hLK) := by
      exact Fintype.prod_equiv
        (abstractFixedFieldCosetEquivAlgHom k Ω K L hLK)
        (fun q : Q =>
          ((Additive.toMul
            (relativeCosetAction (galoisAmbientUnitsRep k Ω)
              K L hLK
              (abstractRelativeFixedFieldUnitsEquivGaloisFixed
                k Ω K L hLK (Additive.ofMul x)) q) : Ωˣ) : Ω))
        (fun σ : abstractRelativeFixedField k Ω hLK →ₐ[
          abstractFixedField k Ω K] Ω =>
            σ (x : abstractRelativeFixedField k Ω hLK))
        (relativeCosetAction_abstractFixedFieldUnit_val
          k Ω K L hLK x)
    _ = algebraMap (abstractFixedField k Ω K) Ω
        (Algebra.norm (abstractFixedField k Ω K)
          (x : abstractRelativeFixedField k Ω hLK)) :=
      (algebraMap_norm_eq_prod_embeddings_of_isSepClosed
        (abstractFixedField k Ω K) Ω
        (abstractRelativeFixedField k Ω hLK)
        (x : abstractRelativeFixedField k Ω hLK)).symm

end Langlands.NYLL.LocalClassFieldTheory

end
