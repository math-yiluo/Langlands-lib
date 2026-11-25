import Langlands.ClassFieldTheory.Global.Artin.FiniteArtin
import Langlands.Global.Arithmetic.ClassFieldStatement
import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.MathlibFrobeniusHilbertComparison
import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ArithmeticUnramifiedPrimeArtin
import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FinitePlaceArtin.Core
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Completion.UnramifiedComparison.LocalNorm
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Completion.UnramifiedComparison.IdealToCompletion
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.IdealMap
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.Frobenius

/-!
# The arithmetic Artin map at every uniformizer and on local units

This file belongs to the Library. It proves that the arithmetic Artin map
`arithmeticFiniteArtin K L` of a finite abelian extension of number fields satisfies the
Library's normalization `Langlands.Global.HasArithmeticArtinNormalization`: at every finite
place `v` of `K` and every prime `w` of `L` above `v` at which `L / K` is unramified, every
uniformizer of the completion `K_v` goes to an arithmetic Frobenius at `w`. It also proves
that the local units at such a place go to `1`.

NYLL proves the Frobenius value at one element of valuation `exp (-1)` per place, chosen by
`Classical.choose` (`FiniteIdeleGroup.chosenLocalOrderSection v 1`), and that its local map
kills the units at a place unramified at NYLL's chosen prime above `v`. The glue here: every
uniformizer is the chosen one times a local unit; a prime above `v` is unramified exactly when
NYLL's chosen prime above `v` is (the two are Galois conjugate); and Mathlib's `IsArithFrobAt`
for the action of `L ≃ₐ[K] L` on `𝓞 L` is the Library's form with
`NumberField.RingOfIntegers.mapAlgHom`.

## Main declarations

* `chosenCentre_isUnramifiedAt`: NYLL's chosen prime above `v` is unramified if some prime
  above `v` is.
* `mul_inv_chosenLocalOrderSection_mem_units`: a uniformizer divided by NYLL's chosen one is
  a local unit.
* `arithmeticFiniteArtin_finiteClassInclusion_of_unit`,
  `arithmeticFiniteArtin_finiteClassInclusion_of_valuation_eq_one`.
* `arithmeticFiniteArtin_finiteClassInclusion_eq_arithFrobAt`: the value at a uniformizer is
  Mathlib's `arithFrobAt (𝓞 K) (L ≃ₐ[K] L) w.asIdeal`.
* `arithmeticFiniteArtin_hasArithmeticArtinNormalization`.
-/

noncomputable section

universe u v

namespace Langlands.ClassFieldTheory.Global.Artin

open Langlands.Global
open scoped NumberField

section Uniformizer

variable {K : Type u} [Field K] [NumberField K]

/-- An element of valuation `exp (-1)` of the completion at `v`, divided by NYLL's chosen
element of order one, is a unit of the valuation ring. -/
theorem mul_inv_chosenLocalOrderSection_mem_units (v : Langlands.Global.FinitePlace K)
    (π : (FiniteCompletion K v)ˣ)
    (hπ : Valued.v (π : FiniteCompletion K v) = WithZero.exp (-1 : ℤ)) :
    π * (FiniteIdeleGroup.chosenLocalOrderSection v 1)⁻¹ ∈
      (v.adicCompletionIntegers K).units := by
  rw [← FiniteIdeleGroup.localOrder_eq_zero_iff, map_mul, map_inv, toAdd_mul, toAdd_inv,
    FiniteIdeleGroup.localOrder_chosenLocalOrderSection, FiniteIdeleGroup.localOrder_apply]
  change -WithZero.log (Valued.v (π : FiniteCompletion K v)) + -1 = 0
  rw [hπ, WithZero.log_exp]
  norm_num

end Uniformizer

variable {K : Type u} {L : Type v} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]

/-- NYLL's chosen prime of `L` above `v` is unramified over `K` if some prime `w` above `v`
is: the primes above `v` are conjugate under `L ≃ₐ[K] L`, so they have the same ramification
index. -/
theorem chosenCentre_isUnramifiedAt (v : Langlands.Global.FinitePlace K)
    (w : Langlands.Global.FinitePlace L) (hw : w.asIdeal.LiesOver v.asIdeal)
    (hunram : Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal) :
    Algebra.IsUnramifiedAt (𝓞 K)
      (finitePlaceExtensionCentre (K := K) (L := L) v
        (chosenFinitePlaceExtension (L := L) v)).asIdeal := by
  let W := finitePlaceExtensionCentre (K := K) (L := L) v (chosenFinitePlaceExtension (L := L) v)
  have hW : W.asIdeal.LiesOver v.asIdeal :=
    finitePlaceExtensionCentre_liesOver (K := K) (L := L) v (chosenFinitePlaceExtension (L := L) v)
  let : Finite (L ≃ₐ[K] L) := IsGaloisGroup.finite (L ≃ₐ[K] L) K L
  let : IsGaloisGroup (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) K L
  have hEw : w.asIdeal.ramificationIdx (𝓞 K) = 1 :=
    (Ideal.ramificationIdx_eq_one_iff).mpr hunram
  have hEQ : W.asIdeal.ramificationIdx (𝓞 K) = w.asIdeal.ramificationIdx (𝓞 K) :=
    Ideal.ramificationIdx_eq_of_isGaloisGroup v.asIdeal W.asIdeal w.asIdeal (L ≃ₐ[K] L)
  exact (Ideal.ramificationIdx_eq_one_iff).mp (hEQ.trans hEw)

/-- At a finite place below a prime unramified in `L`, the arithmetic Artin map kills the
local units. -/
theorem arithmeticFiniteArtin_finiteClassInclusion_of_unit (v : Langlands.Global.FinitePlace K)
    (w : Langlands.Global.FinitePlace L) (hw : w.asIdeal.LiesOver v.asIdeal)
    (hunram : Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal) (a : (FiniteCompletion K v)ˣ)
    (ha : a ∈ (v.adicCompletionIntegers K).units) :
    arithmeticFiniteArtin K L (finiteClassInclusion K v a) = 1 := by
  rw [arithmeticFiniteArtin_finiteClassInclusion,
    GlobalClassFieldTheory.Reciprocity.arithmeticChosenFinitePlaceArtinMonoidHom_apply, inv_eq_one]
  have hChosen := chosenFinitePlaceIsUnramified_of_isUnramifiedAt (K := K) (L := L) v
    (chosenCentre_isUnramifiedAt v w hw hunram)
  have hNorm := adicCompletionIntegerUnits_le_chosenFinitePlaceLocalNormSubgroup
    (K := K) (L := L) v hChosen ha
  rw [← GlobalClassFieldTheory.Reciprocity.chosenFinitePlaceArtinMonoidHom_ker
    (K := K) (L := L) v] at hNorm
  exact hNorm

/-- The same, for a local unit given by its valuation: at a finite place below a prime unramified
in `L`, the arithmetic Artin map kills every element of valuation `1`. -/
theorem arithmeticFiniteArtin_finiteClassInclusion_of_valuation_eq_one
    (v : Langlands.Global.FinitePlace K) (w : Langlands.Global.FinitePlace L)
    (hw : w.asIdeal.LiesOver v.asIdeal) (hunram : Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal)
    (a : (FiniteCompletion K v)ˣ) (ha : Valued.v (a : FiniteCompletion K v) = 1) :
    arithmeticFiniteArtin K L (finiteClassInclusion K v a) = 1 := by
  refine arithmeticFiniteArtin_finiteClassInclusion_of_unit v w hw hunram a ?_
  rw [← FiniteIdeleGroup.localOrder_eq_zero_iff, FiniteIdeleGroup.localOrder_apply]
  change -WithZero.log (Valued.v (a : FiniteCompletion K v)) = 0
  rw [ha, WithZero.log_one, neg_zero]

/-- At a finite place below a prime `w` unramified in `L`, the arithmetic Artin map sends every
uniformizer to Mathlib's arithmetic Frobenius `arithFrobAt` at `w`. -/
theorem arithmeticFiniteArtin_finiteClassInclusion_eq_arithFrobAt
    (v : Langlands.Global.FinitePlace K) (w : Langlands.Global.FinitePlace L)
    (hw : w.asIdeal.LiesOver v.asIdeal) (hunram : Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal)
    (π : (FiniteCompletion K v)ˣ)
    (hπ : Valued.v (π : FiniteCompletion K v) = WithZero.exp (-1 : ℤ)) :
    arithmeticFiniteArtin K L (finiteClassInclusion K v π) =
      arithFrobAt (𝓞 K) (L ≃ₐ[K] L) w.asIdeal := by
  set s := FiniteIdeleGroup.chosenLocalOrderSection v 1
  have hπs : π = (π * s⁻¹) * s := by group
  rw [hπs, map_mul, map_mul,
    arithmeticFiniteArtin_finiteClassInclusion_of_unit v w hw hunram _
      (mul_inv_chosenLocalOrderSection_mem_units v π hπ), one_mul,
    arithmeticFiniteArtin_finiteClassInclusion,
    ← GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin_eq_arithmeticChosenFinitePlaceArtin,
    ClassFieldTheory.GlobalClassFieldComparison.arithmeticPrimeArtin_eq_arithmeticFrobeniusAt
      v w hw hunram]
  rfl

/-- The arithmetic Artin map satisfies the Library's normalization at every uniformizer of
every place unramified in `L`. -/
theorem arithmeticFiniteArtin_hasArithmeticArtinNormalization :
    HasArithmeticArtinNormalization (arithmeticFiniteArtin K L) := by
  intro v w hw hunram π hπ
  rw [arithmeticFiniteArtin_finiteClassInclusion_eq_arithFrobAt v w hw hunram π hπ]
  let : Finite (L ≃ₐ[K] L) := IsGaloisGroup.finite (L ≃ₐ[K] L) K L
  let : IsGaloisGroup (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) K L
  have h := IsArithFrobAt.arithFrobAt (𝓞 K) (L ≃ₐ[K] L) w.asIdeal
  intro x
  exact h x

end Langlands.ClassFieldTheory.Global.Artin
