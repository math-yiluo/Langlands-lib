module

public import Mathlib.RingTheory.AdicCompletion.RingHom
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.QuasiFinite.Basic
public import StacksFrontier.RingTheory.AdicCompletion.FiniteAlgebra

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# Factoring an algebra map through an adic completion

Let `R` and `T` be algebras over a commutative ring `A`, let `I ⊆ R` and `J ⊆ T` be ideals and
let `T` be `J`-adically complete. An `A`-algebra map `R → T` carrying `I` into `J` extends to
the `I`-adic completion of `R`: the maps `R ⧸ Iⁿ → T ⧸ Jⁿ` it induces, precomposed with the
projections of `R^∧`, form a compatible family, and the universal property of a complete ring
turns that family into an `A`-algebra map `R^∧ → T`.

A ring is adically complete along a nilpotent ideal; this is how the hypothesis on `T` is met
when `T` is a nilpotent thickening of a complete ring.

The extension is unique when `I` is finitely generated and `T` is `J`-adically Hausdorff: two
such maps agree on the image of `R`, which is dense for the `I`-adic topology, and the
difference of their values lies in every power of `J`.

## Main results

* `IsAdicComplete.of_isNilpotent`: a ring is adically complete along a nilpotent ideal.
* `AdicCompletion.factorₐ_evalₐ`: the projections of an adic completion form a compatible
  family.
* `AdicCompletion.exists_algHom_of_isAdicComplete`: an `A`-algebra map `R → T` carrying `I`
  into `J`, with `T` `J`-adically complete, extends to the `I`-adic completion of `R`.
* `AdicCompletion.algHom_ext_of_isHausdorff`: two maps out of an adic completion which agree
  on the image of `R` and carry `I` into an ideal of Hausdorffness are equal.
-/

@[expose] public noncomputable section

/-- A ring is adically complete along a nilpotent ideal: the filtration is eventually zero, so
every adic Cauchy sequence is eventually constant and only zero is infinitely divisible. -/
theorem IsAdicComplete.of_isNilpotent {R : Type*} [CommRing R] (I : Ideal R)
    (hI : IsNilpotent I) : IsAdicComplete I R := by
  obtain ⟨k, hk⟩ := hI
  have hbot : (I ^ k • (⊤ : Submodule R R)) = ⊥ := by
    rw [show I ^ k = ⊥ from le_antisymm hk.le bot_le]
    simp
  have hzero : ∀ {x y : R}, x ≡ y [SMOD (I ^ k • ⊤ : Submodule R R)] → x = y := by
    intro x y h
    rwa [hbot, SModEq.bot] at h
  have hh : IsHausdorff I R := ⟨fun x hx => hzero (hx k)⟩
  have hp : IsPrecomplete I R := by
    refine ⟨fun f hf => ⟨f k, fun n => ?_⟩⟩
    rcases le_or_gt n k with hn | hn
    · exact hf hn
    · rw [hzero (hf hn.le)]
  exact ⟨⟩

namespace AdicCompletion

end AdicCompletion

end
