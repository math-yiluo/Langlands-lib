module

public import Mathlib.FieldTheory.FinTrdeg
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Localization.BaseChange
public import StacksFrontier.RingTheory.KrullDimension.FiniteTypeNeTop
public import StacksFrontier.RingTheory.RelativeDimension.Semicontinuity
public import StacksFrontier.RingTheory.RelativeDimension.Basic
public import StacksFrontier.RingTheory.Spectrum.Prime.LocalDimension
public import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.Tactic.CrossRefAttribute

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# Equality of dimensions for a flat local extension of domains

For an injective, flat, essentially finite type local homomorphism of local domains, the
dimension of the closed fibre plus the transcendence degree of the residue-field extension
equals the transcendence degree of the extension of domains.

## Main results

* `IsLocalRing.ringKrullDim_closedFiber_add_trdeg_eq_trdeg` gives the dimension equality.

## Implementation notes

The closed fibre is the quotient of `B` by the extension of the maximal ideal of `A`.
Transcendence degree over domains is written `Algebra.trdeg A B`; this agrees with the
transcendence degree of the corresponding fraction fields. Cardinal-valued transcendence
degrees are sent to `WithBot ℕ∞` by `Cardinal.toENat`.

## References

* [Stacks Project, Tag 053T](https://stacks.math.columbia.edu/tag/053T)
-/

@[expose] public section

namespace IsLocalRing

universe u

open scoped TensorProduct

/-! ### Domains after valuation base change -/

/-! ### Bridges from the Stacks presentation to the algebra APIs -/

theorem relativeDimensionAt_eq_localKrullDim_of_field
    (k : Type*) {S : Type*} [Field k] [CommRing S] [Algebra k S]
    (q : Ideal S) [q.IsPrime] :
    Algebra.relativeDimensionAt k q =
      TopologicalSpace.localKrullDim (PrimeSpectrum S) ⟨q, ‹_›⟩ := by
  have hset : PrimeSpectrum.comap (algebraMap k S) ⁻¹'
      {PrimeSpectrum.comap (algebraMap k S) (⟨q, ‹_›⟩ : PrimeSpectrum S)} = Set.univ :=
    Set.eq_univ_iff_forall.mpr fun _ ↦ Subsingleton.elim _ _
  rw [Algebra.relativeDimensionAt, ← TopologicalSpace.topologicalKrullDimAt_eq_localKrullDim]
  exact topologicalKrullDimAt_eq_of_homeomorph
    ((Homeomorph.setCongr hset).trans (Homeomorph.Set.univ (PrimeSpectrum S))) _

end IsLocalRing
