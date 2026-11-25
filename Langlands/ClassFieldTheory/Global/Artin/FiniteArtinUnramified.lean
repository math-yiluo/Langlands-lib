import Langlands.ClassFieldTheory.Global.Artin.ArtinUniqueness
import Langlands.ClassFieldTheory.Global.Artin.FiniteArtinNormalization
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.LocalComponent
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Relative.FinitePlaceTensorNorm
import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.PublicRayClassComparison
import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.ArithmeticNormalization
import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.LocalGlobalArtinCompatibility.Factorization
import Nyll.ClassFieldTheory.Theorems.ConductorsAndRayClassFields.AbelianConductorFiniteNormCriterion
import Nyll.ClassFieldTheory.Theorems.ConductorsAndRayClassFields.AbelianConductorFiniteUnramified
import Nyll.ClassFieldTheory.Theorems.ConductorsAndRayClassFields.RayLocalHigherUnitZero
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# The arithmetic Artin map on local units and ramification

This file belongs to the Library. For a finite abelian extension of number fields `L / K` and a
finite place `v` of `K`, it describes the kernel of the arithmetic Artin map
`arithmeticFiniteArtin K L` on the one-place idèle classes at `v` as the local norm group, the
image of the norm of the `K_v`-algebra `K_v ⊗[K] L`, and proves the unit criterion: the
arithmetic Artin map kills the local units at `v` exactly when every prime of `L` above `v` is
unramified over `K`.

One direction is in `FiniteArtinNormalization.lean`. For the other, NYLL's local–global
compatibility identifies the arithmetic Artin map at `v` with the inverse of its chosen local
Artin map, whose kernel is the norm group of the completion at a chosen prime above `v`, which
NYLL identifies with the image of the norm of `K_v ⊗[K] L`. If the local units lie in it, the
exponent at `v` of the conductor of `L / K` is `0` (NYLL's conductor criterion at depth `0`, where
the higher-unit group is the group of units), and a place where the conductor has exponent `0` is
unramified in `L`.

## Main declarations

* `arithmeticFiniteArtin_finiteClassInclusion_eq_one_iff`: the kernel at `v` is the local norm
  group.
* `isUnramifiedAt_of_arithmeticFiniteArtin_finiteClassInclusion_eq_one`: the unit criterion.
* `arithmeticFiniteArtin_finiteClassInclusion_units_eq_one_iff`: both directions.

## Sources

Neukirch, *Algebraic Number Theory*, Chapter VI, Corollary (5.8), p. 394
(`N_{L|K} C_L ∩ K_𝔭^* = N_𝔭 L_𝔓^*`), Definition (6.4) and Proposition (6.5), p. 397 (the
conductor is the product of the local conductors), Corollary (6.6), p. 398 (`𝔭` is ramified in
`L` if and only if `𝔭` divides the conductor); Chapter V, Definition (1.6) and Proposition (1.7),
p. 323 (the local conductor; `L_𝔓 | K_𝔭` is unramified if and only if `U_𝔭 ⊆ N L_𝔓^*`).
-/

noncomputable section

universe u v

namespace Langlands.ClassFieldTheory.Global.Artin

open Langlands.Global
open scoped NumberField TensorProduct

variable {K : Type u} {L : Type v} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]

/-- At a finite place `v`, the arithmetic Artin map kills the one-place idèle class of `a`
exactly when `a` is a norm from the `K_v`-algebra `K_v ⊗[K] L`. -/
theorem arithmeticFiniteArtin_finiteClassInclusion_eq_one_iff
    (v : Langlands.Global.FinitePlace K) (a : (FiniteCompletion K v)ˣ) :
    arithmeticFiniteArtin K L (finiteClassInclusion K v a) = 1 ↔
      a ∈ (Units.map (Algebra.norm (FiniteCompletion K v)) :
        (FiniteCompletion K v ⊗[K] L)ˣ →* (FiniteCompletion K v)ˣ).range := by
  rw [arithmeticFiniteArtin_finiteClassInclusion,
    GlobalClassFieldTheory.Reciprocity.arithmeticChosenFinitePlaceArtinMonoidHom_apply, inv_eq_one,
    GlobalClassFieldTheory.Reciprocity.chosenFinitePlaceArtinMonoidHom_eq_one_iff_chosenLocalNorm,
    ← finitePlaceLocalTensorNorm_range_eq_chosenLocalNormSubgroup]
  rfl

/-- **The unit criterion.** If the arithmetic Artin map of `L / K` kills the local units at a
finite place `v`, every prime of `L` above `v` is unramified over `K`. -/
theorem isUnramifiedAt_of_arithmeticFiniteArtin_finiteClassInclusion_eq_one
    (v : Langlands.Global.FinitePlace K)
    (h : ∀ a : (FiniteCompletion K v)ˣ, a ∈ (v.adicCompletionIntegers K).units →
      arithmeticFiniteArtin K L (finiteClassInclusion K v a) = 1)
    (w : Langlands.Global.FinitePlace L) (hw : w.asIdeal.LiesOver v.asIdeal) :
    Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal := by
  have hle : (v.adicCompletionIntegers K).units ≤
      (Units.map (Algebra.norm (v.adicCompletion K)) :
        (v.adicCompletion K ⊗[K] L)ˣ →* (v.adicCompletion K)ˣ).range := fun a ha =>
    (arithmeticFiniteArtin_finiteClassInclusion_eq_one_iff v a).1 (h a ha)
  have hc := ClassFieldTheory.normFullConductor_isAbelianConductor K L
  have h0 := (hc.finiteExponent_le_iff_higherUnit_le_tensorNorm v 0).2
    (by rw [ClassFieldTheory.rayLocalHigherUnitGroup_zero]; exact hle)
  exact (hc.finiteExponent_eq_zero_iff_unramified v).1 (Nat.le_zero.1 h0) w hw

/-- The arithmetic Artin map of `L / K` kills the local units at a finite place `v` if and only
if every prime of `L` above `v` is unramified over `K`. -/
theorem arithmeticFiniteArtin_finiteClassInclusion_units_eq_one_iff
    (v : Langlands.Global.FinitePlace K) :
    (∀ a : (FiniteCompletion K v)ˣ, a ∈ (v.adicCompletionIntegers K).units →
      arithmeticFiniteArtin K L (finiteClassInclusion K v a) = 1) ↔
      ∀ w : Langlands.Global.FinitePlace L, w.asIdeal.LiesOver v.asIdeal →
        Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal := by
  refine ⟨fun h => isUnramifiedAt_of_arithmeticFiniteArtin_finiteClassInclusion_eq_one v h,
    fun h a ha => ?_⟩
  obtain ⟨w, hw⟩ := exists_liesOver K L v
  exact arithmeticFiniteArtin_finiteClassInclusion_of_unit v w hw (h w hw) a ha

end Langlands.ClassFieldTheory.Global.Artin
