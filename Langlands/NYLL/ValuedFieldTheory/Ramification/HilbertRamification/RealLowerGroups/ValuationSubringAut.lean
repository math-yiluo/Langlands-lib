/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 1199, 2026-11-01, with source extraction and parameter
analysis contributed by Worker 106: isolate M304.014 from upstream commit
fbd320cd8b1b06487c58227e92eb135794267709, prefix namespaces with
Langlands.NYLL, and specialize the published closed preservation theorem
for each membership witness. Retain the four independent universes,
the supplied algebra, and the original structure-field proofs.
Retained license and notices: licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.RealLowerGroups.AutomorphismProof
import Mathlib.FieldTheory.Galois.Basic

/-!
# The actual valuation-ring automorphism from unique extension

This isolates M304.014, lines 164–182 of the pinned `RealLowerGroups.lean`.
The map restricts the supplied field automorphism and its inverse to the
very chosen target valuation ring.
-/

universe u v w x

namespace Langlands.NYLL.RamificationTheory.HilbertRamification.Higher

open Langlands.NYLL.RamificationTheory.DiscreteValuationField.DVF

variable {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
variable {base : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{u, v} K}
variable {target : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{w, x} L}
variable [base.valuation.HasExtension target.valuation]

/-- The automorphism induced on the target valuation ring by uniqueness of the
valuation extension. -/
def valuationSubringAutOfUniqueExtension
    (huniq : HasUniqueValuationExtension.{u, v, w, x, x} base target)
    (σ : Gal(L/K)) :
    target.valuationSubring ≃+* target.valuationSubring where
  toFun a :=
    ⟨σ (a : L),
      (@mem_valuationSubring_algEquiv_iff_of_hasUniqueValuationExtension.{u, v, w, x}
        K L _ _ _ base target _ huniq σ (a : L)).1 a.property⟩
  invFun a :=
    ⟨σ⁻¹ (a : L),
      (@mem_valuationSubring_algEquiv_iff_of_hasUniqueValuationExtension.{u, v, w, x}
        K L _ _ _ base target _ huniq σ⁻¹ (a : L)).1 a.property⟩
  left_inv a := Subtype.ext (σ.symm_apply_apply a)
  right_inv a := Subtype.ext (σ.apply_symm_apply a)
  map_mul' a b := Subtype.ext (map_mul σ (a : L) (b : L))
  map_add' a b := Subtype.ext (map_add σ (a : L) (b : L))

end Langlands.NYLL.RamificationTheory.HilbertRamification.Higher
