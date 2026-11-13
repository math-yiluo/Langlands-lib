/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 121, 2026-11-13: extract the data declarations
M243.001–M243.006 (lines 42–94: `decompositionFixedSubring`,
`decompositionFixedMaximalIdeal`, `decompositionResidueField`,
`selectedResidueField`, `decompositionFieldValuationSubring`,
`decompositionFieldValuationSubringEquivFixedSubring`) of
`Nyll/ValuedFieldTheory/Ramification/HilbertRamification/ResidueExactSequence.lean`
at upstream commit fbd320cd8b1b06487c58227e92eb135794267709; prefix the
namespace with Langlands.NYLL. The universes, section variables (including
the unused `[IsGalois K L]`), docstrings and definitions, with the proofs of
the ring-equivalence fields, are unchanged. The NYLL imports
`Nyll.ValuedFieldTheory.Ramification.ClosedSubgroups` and
`Nyll.ValuedFieldTheory.Ramification.ProfiniteInvariant` are replaced by the
published M239 data module and the Mathlib modules those two files import.
`open scoped Pointwise Topology` is omitted, being unused here. All other
declarations of the source file are omitted.
Retained license and notices: licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ValuationSubring.Definitions
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.RingTheory.Invariant.Profinite

/-!
# The residue-action exact sequence: fixed-subring data

For a valuation subring `A` of `L` and the decomposition group `G_w` of `A`
over `K`: the fixed subring `A^{G_w}` of `A`, the contraction of the maximal
ideal of `A` to it, the quotient `κ` by this contraction, the residue field
`λ` of `A`, the valuation subring `A ∩ Z_w` of the decomposition field, and
the ring isomorphism `A ∩ Z_w ≃+* A^{G_w}` (NYLL M243.001–.006).
-/

namespace Langlands.NYLL.RamificationTheory

noncomputable section

universe u v

namespace HilbertRamification
namespace ValuationSubring

variable (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
variable [IsGalois K L]

/-- The valuation ring on the decomposition field, represented inside the
chosen valuation ring as the fixed subring of the decomposition group. -/
abbrev decompositionFixedSubring (A : _root_.ValuationSubring L) : Subring A :=
  FixedPoints.subring A (decompositionGroup K A)

/-- The maximal ideal of the decomposition-field valuation ring. -/
abbrev decompositionFixedMaximalIdeal (A : _root_.ValuationSubring L) :
    Ideal (decompositionFixedSubring K A) :=
  (IsLocalRing.maximalIdeal A).comap (decompositionFixedSubring K A).subtype

/-- The actual base residue field `κ` in the residue-action exact sequence. -/
abbrev decompositionResidueField (A : _root_.ValuationSubring L) :=
  decompositionFixedSubring K A ⧸ decompositionFixedMaximalIdeal K A

/-- The actual target residue field `λ`. -/
abbrev selectedResidueField (A : _root_.ValuationSubring L) :=
  IsLocalRing.ResidueField A

/-- The literal valuation ring on the classical decomposition field `Z_w`. -/
abbrev decompositionFieldValuationSubring
    (A : _root_.ValuationSubring L) :
    _root_.ValuationSubring (decompositionField K A) :=
  A.comap (decompositionField K A).val

/-- The fixed-subring presentation used in the residue-action exact sequence is canonically
the literal valuation ring on `Z_w`. -/
def decompositionFieldValuationSubringEquivFixedSubring
    (A : _root_.ValuationSubring L) :
    decompositionFieldValuationSubring K A ≃+*
      decompositionFixedSubring K A where
  toFun z :=
    ⟨⟨((z : decompositionField K A) : L), z.property⟩, by
      intro sigma
      apply Subtype.ext
      change ((sigma : decompositionGroup K A) : L ≃ₐ[K] L)
          ((z : decompositionField K A) : L) =
        ((z : decompositionField K A) : L)
      exact (IntermediateField.mem_fixedField_iff
        (H := decompositionGroup K A) ((z : decompositionField K A) : L)).mp
          (z : decompositionField K A).property
          (sigma : L ≃ₐ[K] L) sigma.property⟩
  invFun r := by
    let z : decompositionField K A :=
      ⟨((r : A) : L), by
        rw [IntermediateField.mem_fixedField_iff]
        intro sigma hsigma
        have hr := r.property ⟨sigma, hsigma⟩
        exact congrArg Subtype.val hr⟩
    exact ⟨z, r.val.property⟩
  left_inv z := by ext; rfl
  right_inv r := by ext; rfl
  map_add' _ _ := by ext; rfl
  map_mul' _ _ := by ext; rfl

end ValuationSubring
end HilbertRamification

end
end Langlands.NYLL.RamificationTheory
