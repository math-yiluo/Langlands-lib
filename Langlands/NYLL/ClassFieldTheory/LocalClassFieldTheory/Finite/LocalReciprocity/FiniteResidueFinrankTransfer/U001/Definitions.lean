/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Adapted by Worker 85, 14 November 2026: extracted the source definition
LocalClassFieldTheory.valuationSubringEquivDecompositionFieldOfEqTop
(inventory M252.001) as
Langlands.NYLL.LocalClassFieldTheory.valuationSubringEquivDecompositionFieldOfEqTop.
The universes, binders, type and body, including the proofs of the
membership and ring-equivalence fields, are unchanged. The namespace is
prefixed with Langlands.NYLL; the NYLL imports are replaced by the published
module defining decompositionFieldValuationSubring; the opens of the unused
namespaces CyclicCohomology, ClassFormation, LocalFieldTheory and
ValuationTheory and the unused `open scoped ValuativeRel` are omitted. All
other source declarations are omitted. The retained license and notice are
licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ResidueExactSequence.Definitions

/-!
# The decomposition-field valuation ring when the decomposition group is everything

Source: Naganori Yamaguchi, ClassFieldTheory, commit
fbd320cd8b1b06487c58227e92eb135794267709,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteResidueFinrankTransfer.lean`,
lines 23–34 (namespace, opens, universes) and 36–89 (inventory M252.001).
-/

namespace Langlands.NYLL.LocalClassFieldTheory
open RamificationTheory

noncomputable section

open HilbertRamification.ValuationSubring

universe u v

/-- If the decomposition group of an ambient valuation ring is the whole
Galois group, its decomposition-field valuation ring is canonically
equivalent to the given valuation ring on the ground field. -/
noncomputable def valuationSubringEquivDecompositionFieldOfEqTop
    {F : Type u} {Omega : Type v} [Field F] [Field Omega] [Algebra F Omega]
    [IsGalois F Omega]
    (A : ValuationSubring Omega) (C : ValuationSubring F)
    (hC : A.comap (algebraMap F Omega) = C)
    (hA : decompositionGroup F A = ⊤) :
    C ≃+* decompositionFieldValuationSubring F A := by
  let Z := decompositionField F A
  have hZ : Z = ⊥ := by
    change IntermediateField.fixedField (decompositionGroup F A) = ⊥
    rw [hA]
    simpa using
      (InfiniteGalois.fixedField_fixingSubgroup
        (⊥ : IntermediateField F Omega))
  let eFZ : F ≃ₐ[F] Z :=
    (IntermediateField.botEquiv F Omega).symm.trans
      (IntermediateField.equivOfEq hZ.symm)
  refine
    { toFun := fun x => ⟨eFZ (x : F), ?_⟩
      invFun := fun z => ⟨eFZ.symm (z : Z), ?_⟩
      left_inv := fun x => by
        apply Subtype.ext
        exact eFZ.symm_apply_apply (x : F)
      right_inv := fun z => by
        apply Subtype.ext
        exact eFZ.apply_symm_apply (z : Z)
      map_add' := fun x y => by
        apply Subtype.ext
        exact map_add eFZ (x : F) (y : F)
      map_mul' := fun x y => by
        apply Subtype.ext
        exact map_mul eFZ (x : F) (y : F) }
  · change ((eFZ x : Z) : Omega) ∈ A
    have he : ((eFZ x : Z) : Omega) =
        algebraMap F Omega (x : F) := by
      rfl
    rw [he]
    have hx : (x : F) ∈ A.comap (algebraMap F Omega) := by
      rw [hC]
      exact x.property
    exact hx
  · have hz : eFZ.symm (z : Z) ∈ A.comap (algebraMap F Omega) := by
      change algebraMap F Omega (eFZ.symm (z : Z)) ∈ A
      have he : algebraMap F Omega (eFZ.symm (z : Z)) =
          ((z : Z) : Omega) := by
        exact congrArg Subtype.val (eFZ.apply_symm_apply (z : Z))
      rw [he]
      exact z.property
    rw [hC] at hz
    exact hz

end
end Langlands.NYLL.LocalClassFieldTheory
