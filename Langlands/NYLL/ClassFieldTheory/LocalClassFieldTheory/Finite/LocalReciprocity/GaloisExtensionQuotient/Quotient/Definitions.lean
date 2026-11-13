/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.GaloisExtensionQuotient.Initial.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.GaloisExtensionQuotient.Initial.U002.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.GaloisExtensionQuotient.Initial.U008.Proofs
import Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions
import Mathlib.FieldTheory.Galois.Infinite

/-!
# The abstract base-fixing extension quotient is the actual Galois group

Adapted by Worker 57 from NYLL commit
`fbd320cd8b1b06487c58227e92eb135794267709`, units M089.009 and M089.011 of
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/GaloisExtensionQuotient.lean`.
The namespace is prefixed with `Langlands.NYLL` and the source imports are
replaced by the published modules supplying the used declarations. The body of
`baseFixingExtensionQuotientEquivAmbient` cites the source theorem
`baseFixingToAmbientQuotient_ker` (M089.007), which is not proved in the
Library; that proof argument is replaced by the source proof of M089.007,
written inline. See the paired Markdown for the declaration map and complete
modification record. The original license and notices are retained in
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory
open RamificationTheory CyclicCohomology

noncomputable section

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]

/-- The abstract class-formation quotient for `E/K` is the ordinary quotient of the
ambient Galois group by the subgroup fixing `E`. -/
def baseFixingExtensionQuotientEquivAmbient
    (E : IntermediateField K Ω) [IsGalois K E] :
    ((closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω)).toSubgroup ⧸
      extensionSubgroup
        (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
        (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E)) ≃*
      Gal(Ω / K) ⧸ (closedFixingSubgroup K Ω E).toSubgroup :=
  (QuotientGroup.quotientMulEquivOfEq
      (show (baseFixingToAmbientQuotient K Ω E).ker =
          extensionSubgroup
            (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
            (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E) by
        ext x
        change
          (QuotientGroup.mk' (closedFixingSubgroup K Ω E).toSubgroup x.1 = 1) ↔
            x.1 ∈ (closedFixingSubgroup K Ω E).toSubgroup
        exact QuotientGroup.eq_one_iff x.1).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (baseFixingToAmbientQuotient K Ω E)
      (baseFixingToAmbientQuotient_surjective K Ω E))

/-- The exact quotient group appearing in the abstract class-formation framework for the normal
intermediate extension `E/K` is canonically the actual `Gal(E/K)`. -/
def baseFixingExtensionQuotientEquivGaloisGroup
    (E : IntermediateField K Ω) [IsGalois K E] :
    ((closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω)).toSubgroup ⧸
      extensionSubgroup
        (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
        (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E)) ≃*
      Gal(E / K) := by
  let H : ClosedSubgroup (Gal(Ω / K)) := closedFixingSubgroup K Ω E
  letI : H.toSubgroup.Normal := closedFixingSubgroup_normal K Ω E
  exact (baseFixingExtensionQuotientEquivAmbient K Ω E).trans
    ((InfiniteGalois.normalAutEquivQuotient H).trans
      (AlgEquiv.autCongr
        (IntermediateField.equivOfEq
          (InfiniteGalois.fixedField_fixingSubgroup E))))

end
end Langlands.NYLL.LocalClassFieldTheory
