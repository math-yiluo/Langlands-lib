/-
Ported from `Theorems/Thm_HopfAlgebra_faithfullyFlat_of_flat_of_injective_of_isAlgClosed.lean` of the Anthropic FLT formalization,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2. Copyright 2026 Anthropic, PBC.
Licensed under Apache License 2.0; see licenses/Anthropic-FLT/LICENSE, NOTICE,
and ATTRIBUTION.md. Imports are prefixed; utility commands are replaced by
standard Lean commands. See the paired Markdown for changes and provenance.
-/
import Mathlib
import Langlands.AnthropicFLT.P2M.Sol.S_HopfAlgebra_faithfullyFlat_of_flat_of_injective_of_isAlgClosed
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

open scoped TensorProduct

universe u v w

theorem HopfAlgebra.faithfullyFlat_of_flat_of_injective_of_isAlgClosed
    {k : Type u} [Field k] [IsAlgClosed k]
    (K : Type v) [CommRing K] [HopfAlgebra k K] [Algebra.FiniteType k K]
    (H : Type w) [CommRing H] [HopfAlgebra k H] [Algebra.FiniteType k H]
    [Algebra K H] [IsScalarTower k K H] (hinj : Function.Injective (algebraMap K H))
    (hcomul : ∀ x : K, Coalgebra.comul (R := k) (algebraMap K H x) =
      TensorProduct.map (IsScalarTower.toAlgHom k K H).toLinearMap (IsScalarTower.toAlgHom k K H).toLinearMap
        (Coalgebra.comul (R := k) x))
    (hcounit : ∀ x : K, Coalgebra.counit (R := k) (algebraMap K H x) = Coalgebra.counit (R := k) x)
    [Module.Flat K H] :
    Module.FaithfullyFlat K H := by
  exact _root_.P2MW.S_HopfAlgebra_faithfullyFlat_of_flat_of_injective_of_isAlgClosed.solution (k := k) K H hinj hcomul hcounit
