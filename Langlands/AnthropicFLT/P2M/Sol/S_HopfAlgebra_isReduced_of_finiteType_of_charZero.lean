/-
Ported from `P2M/Sol/S_HopfAlgebra_isReduced_of_finiteType_of_charZero.lean` of the Anthropic FLT formalization,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2. Copyright 2026 Anthropic, PBC.
Licensed under Apache License 2.0; see licenses/Anthropic-FLT/LICENSE, NOTICE,
and ATTRIBUTION.md. Imports are prefixed; utility commands are replaced by
standard Lean commands. See the paired Markdown for changes and provenance.
-/
import Mathlib.RingTheory.HopfAlgebra.TensorProduct
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.Flat.Basic
import Langlands.AnthropicFLT.Theorems.Thm_HopfAlgebra_isReduced_of_finiteType_of_isAlgClosed_of_charZero
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_isReduced_of_finiteType_of_charZero

set_option maxHeartbeats 3200000
open scoped TensorProduct

theorem solution
    (K : Type*) [Field K] [CharZero K]
    (A : Type*) [CommRing A] [HopfAlgebra K A] [Algebra.FiniteType K A] :
    IsReduced A := by
  let Ω := AlgebraicClosure K

  haveI : IsReduced (Ω ⊗[K] A) :=
    HopfAlgebra.isReduced_of_finiteType_of_isAlgClosed_of_charZero Ω (Ω ⊗[K] A)

  have hinj : Function.Injective
      (Algebra.TensorProduct.includeRight : A →ₐ[K] Ω ⊗[K] A) :=
    Algebra.TensorProduct.includeRight_injective (R := K) (A := Ω) (B := A)
      (algebraMap K Ω).injective
  exact isReduced_of_injective
    (Algebra.TensorProduct.includeRight : A →ₐ[K] Ω ⊗[K] A).toRingHom hinj
