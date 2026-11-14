/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Adapted by Worker 85, 14 November 2026: extracted the source private
definition LocalClassFieldTheory.localBaseValuationSubringEquivDecompositionField
(inventory M249.011) as Langlands.NYLL.PortInternal.M249.d011 and the source
definition LocalClassFieldTheory.localBaseResidueEquivDecompositionResidue
(inventory M249.012) as
Langlands.NYLL.LocalClassFieldTheory.localBaseResidueEquivDecompositionResidue,
from lines 31–46 and 176–233 of
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/LocalResidueDatum.lean
at upstream commit fbd320cd8b1b06487c58227e92eb135794267709. The private
definition is made public under the port-internal name, and its docstring is
prefixed with the inventory identifier and source name; its type and tactic
body are unchanged. The body of M249.012 is unchanged except that its
reference to the private definition uses the port-internal name. The
namespace of M249.012 is prefixed with Langlands.NYLL; the source imports are
replaced by the published modules supplying the two theorems used in the body
of M249.011, decompositionFieldResidueEquiv and the CompleteDVF projections;
the opens are replaced by fully qualified opens of the namespaces used, and
unused opens are omitted. All other source declarations are omitted. The
retained license and notice are licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.LocalResidueDatum.U007.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.LocalResidueDatum.U010.Proofs
import Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ResidueExactSequence.ResidueComparison
import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Complete.Projections

/-!
# The base residue field of the chosen separable valuation ring

Source: Naganori Yamaguchi, ClassFieldTheory, commit
fbd320cd8b1b06487c58227e92eb135794267709,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/LocalResidueDatum.lean`,
lines 31–46 (namespace, opens, section variables), 176–223 (inventory
M249.011) and 225–233 (inventory M249.012).

For a nonarchimedean local field `K`, the decomposition group of the chosen
valuation ring of `SeparableClosure K` is everything, so the decomposition
field is `K` itself.  This identifies the valuation ring of the canonical
complete discrete valuation of `K` with the decomposition-field valuation ring
(M249.011), and hence the residue field of `K` with the decomposition residue
field of the residue-action exact sequence (M249.012).
-/

noncomputable section

namespace Langlands.NYLL.PortInternal.M249

open Langlands.NYLL.LocalFieldTheory Langlands.NYLL.LocalClassFieldTheory
open Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- M249.011 (source private `localBaseValuationSubringEquivDecompositionField`):
when the decomposition subgroup is top, the valuation ring on the
decomposition field is the original local valuation ring. -/
noncomputable def d011 :
    (localCompleteDVF K).valuationSubring ≃+*
      decompositionFieldValuationSubring K
        (localSeparableValuationSubring K) := by
  let A := localSeparableValuationSubring K
  let Z := decompositionField K A
  have hZ : Z = ⊥ := by
    change IntermediateField.fixedField (decompositionGroup K A) = ⊥
    rw [localSeparableDecompositionGroup_eq_top K]
    simpa using
      (InfiniteGalois.fixedField_fixingSubgroup
        (⊥ : IntermediateField K (SeparableClosure K)))
  let eKZ : K ≃ₐ[K] Z :=
    (IntermediateField.botEquiv K (SeparableClosure K)).symm.trans
      (IntermediateField.equivOfEq hZ.symm)
  refine
    { toFun := fun x => ⟨eKZ (x : K), ?_⟩
      invFun := fun z => ⟨eKZ.symm (z : Z), ?_⟩
      left_inv := fun x => by
        apply Subtype.ext
        exact eKZ.symm_apply_apply (x : K)
      right_inv := fun z => by
        apply Subtype.ext
        exact eKZ.apply_symm_apply (z : Z)
      map_add' := fun x y => by
        apply Subtype.ext
        exact map_add eKZ (x : K) (y : K)
      map_mul' := fun x y => by
        apply Subtype.ext
        exact map_mul eKZ (x : K) (y : K) }
  · change ((eKZ x : Z) : SeparableClosure K) ∈ A
    have he : ((eKZ x : Z) : SeparableClosure K) =
        algebraMap K (SeparableClosure K) (x : K) := by
      rfl
    rw [he]
    exact (localSeparableValuationSubring_pullback K (x : K)).2 x.property
  · change eKZ.symm (z : Z) ∈
      (localCompleteDVF K).valuation.valuationSubring
    apply (localSeparableValuationSubring_pullback K (eKZ.symm (z : Z))).1
    have he : algebraMap K (SeparableClosure K) (eKZ.symm (z : Z)) =
        ((z : Z) : SeparableClosure K) := by
      exact congrArg Subtype.val (eKZ.apply_symm_apply (z : Z))
    rw [he]
    exact z.property

end Langlands.NYLL.PortInternal.M249

namespace Langlands.NYLL.LocalClassFieldTheory

open Langlands.NYLL.LocalFieldTheory
open Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The residue field in the residue-action exact sequence is canonically the finite residue
field of the original local field. -/
noncomputable def localBaseResidueEquivDecompositionResidue :
    (localCompleteDVF K).residueField ≃+*
      decompositionResidueField K (localSeparableValuationSubring K) :=
  (IsLocalRing.ResidueField.mapEquiv
      (Langlands.NYLL.PortInternal.M249.d011 K)).trans
    (decompositionFieldResidueEquiv (K := K)
      (localSeparableValuationSubring K))

end Langlands.NYLL.LocalClassFieldTheory

end
