module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.Nilpotent.Lemmas
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppRamificationTransport
public import StacksFrontier.RingTheory.Ideal.NilradicalQuotient
public import StacksFrontier.RingTheory.DiscreteValuationRing.Solution

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# Transporting weak solutions across isomorphisms of base-change data

Let `D` and `D'` be two base-change packages
(`IsDiscreteValuationRing.IntegralClosureBaseChange`). If their recorded base rings and upper rings
are identified by ring isomorphisms `eA : D.A₁ ≃+* D'.A₁` and `eB : D.B₁ ≃+* D'.B₁` commuting with
the structure maps, then `D` is a weak solution if and only if `D'` is. This applies in particular
when both packages are base changes along one field `K₂`, the first of the tower obtained from the
second by a base change along `K₁ / K` (Stacks Tag 09F9): then `(M ⊗[K] K₁) ⊗[K₁] K₂ ≅ M ⊗[K] K₂`,
and the integral closures of `A₁` and of `A` in `K₂` agree since `A₁` is integral over `A`.

## Main definitions

* `Stacks.DiscreteValuationRing.EppLevelInduction.reductionRingEquiv`: the isomorphism of
  reductions `X ⧸ nilradical X ≃+* Y ⧸ nilradical Y` induced by a ring isomorphism `X ≃+* Y`.
* `Stacks.DiscreteValuationRing.EppLevelInduction.integralClosureRingEquivOfAlgEquiv`: the ring
  isomorphism of integral closures induced by an algebra isomorphism of the ambient rings.
* `Stacks.DiscreteValuationRing.EppLevelInduction.ringEquivOfIsIntegralClosureTower`: the
  isomorphism of two integral closures in one ring over bases one of which is integral over the
  other.
* `Stacks.DiscreteValuationRing.EppLevelInduction.compositumRingEquiv`: the isomorphism of the
  recorded composita of two packages induced by an isomorphism `M₁ ⊗[K₁] K₂ ≃+* M ⊗[K] K₂`.

## Main results

* `Stacks.DiscreteValuationRing.EppLevelInduction.nonempty_algEquiv_tensorCancel` and
  `Stacks.DiscreteValuationRing.EppLevelInduction.exists_ringEquiv_tensorCancel_includeRight`:
  `(M ⊗[K] K₁) ⊗[K₁] K₂ ≅ M ⊗[K] K₂`.
* `Stacks.DiscreteValuationRing.EppLevelInduction.rightAlgebra_eq_includeRight_toAlgebra`: the
  two algebra structures on `A ⊗[R] B` over the right factor are equal.
* `Stacks.DiscreteValuationRing.EppLevelInduction.isWeakSolution_of_ringEquiv_square` and
  `Stacks.DiscreteValuationRing.EppLevelInduction.isWeakSolution_iff_ringEquiv_square`:
  `IsWeakSolution` transports across a commuting square of ring isomorphisms of the two
  packages' base and upper rings.
* `Stacks.DiscreteValuationRing.EppLevelInduction.isIntegralClosure_tower_bot`: an integral
  closure over `S` is one over `R` when `S` is integral over `R`.
* `Stacks.DiscreteValuationRing.EppLevelInduction.isWeakSolution_of_fractionFieldRingEquiv` and
  `Stacks.DiscreteValuationRing.EppLevelInduction.isWeakSolution_of_tensorCancel`: the transport
  for two packages over one field `K₂`, with the compatibilities stated in `K₂` and in the
  composita.

## References

* [The Stacks Project, Tag 09EN](https://stacks.math.columbia.edu/tag/09EN)
* [The Stacks Project, Tag 09F5](https://stacks.math.columbia.edu/tag/09F5)
* [The Stacks Project, Tag 09F9](https://stacks.math.columbia.edu/tag/09F9)
-/

@[expose] public section

open scoped TensorProduct

namespace Stacks.DiscreteValuationRing.EppLevelInduction

/-! ### The base-change cancellation -/

open IsDiscreteValuationRing

universe uA uB uK uL uK₁ w₁ w₂ w₃ vA vB vK vL vK₁ x₁ x₂ x₃

section Bridge

variable {A : Type uA} {B : Type uB} {K : Type uK} {L : Type uL} {K₁ : Type uK₁}
    [CommRing A] [CommRing B] [Field K] [Field L] [Field K₁]
    [IsDomain A] [IsDomain B] [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L]
    [Algebra K L] [Algebra K K₁] [Algebra A K₁]
    [IsExtension A B] [IsFractionRing A K] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L] [IsScalarTower A K K₁]
    [Module.Finite K K₁]
    {A' : Type vA} {B' : Type vB} {K' : Type vK} {L' : Type vL} {K₁' : Type vK₁}
    [CommRing A'] [CommRing B'] [Field K'] [Field L'] [Field K₁']
    [IsDomain A'] [IsDomain B'] [IsDiscreteValuationRing A'] [IsDiscreteValuationRing B']
    [Algebra A' B'] [Algebra A' K'] [Algebra A' L'] [Algebra B' L']
    [Algebra K' L'] [Algebra K' K₁'] [Algebra A' K₁']
    [IsExtension A' B'] [IsFractionRing A' K'] [IsFractionRing B' L']
    [IsScalarTower A' B' L'] [IsScalarTower A' K' L'] [IsScalarTower A' K' K₁']
    [Module.Finite K' K₁']

/-- If ring isomorphisms `eA : D.A₁ ≃+* D'.A₁` and `eB : D.B₁ ≃+* D'.B₁` commute with the structure
maps, then `D'` is a weak solution whenever `D` is. -/
theorem isWeakSolution_of_ringEquiv_square
    (D : IntegralClosureBaseChange.{uA, uB, uK, uL, uK₁, w₁, w₂, w₃} A B K L K₁)
    (D' : IntegralClosureBaseChange.{vA, vB, vK, vL, vK₁, x₁, x₂, x₃} A' B' K' L' K₁') :
    letI := D.commRingA₁
    letI := D.commRingB₁
    letI := D.algebraA₁B₁
    letI := D'.commRingA₁
    letI := D'.commRingB₁
    letI := D'.algebraA₁B₁
    ∀ (eA : D.A₁ ≃+* D'.A₁) (eB : D.B₁ ≃+* D'.B₁),
      (∀ x : D.A₁, algebraMap D'.A₁ D'.B₁ (eA x) = eB (algebraMap D.A₁ D.B₁ x)) →
        D.IsWeakSolution → D'.IsWeakSolution := by
  let := D.commRingA₁
  let := D.commRingB₁
  let := D.algebraA₁B₁
  let := D'.commRingA₁
  let := D'.commRingB₁
  let := D'.algebraA₁B₁
  intro eA eB hsq h q' hq'
  have hmax : (q'.comap (eB : D.B₁ →+* D'.B₁)).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective (eB : D.B₁ →+* D'.B₁) eB.surjective
  have htr := ramificationIdx_map eA eB hsq (q'.comap (eB : D.B₁ →+* D'.B₁))
  rw [Ideal.map_comap_of_surjective (eB : D.B₁ →+* D'.B₁) eB.surjective q'] at htr
  rw [← htr]
  exact h _ hmax

end Bridge

/-! ### Building the bridge's isomorphisms from a base-change step -/

/-- The isomorphism of reductions `X ⧸ nilradical X ≃+* Y ⧸ nilradical Y` induced by a ring
isomorphism `e : X ≃+* Y`. -/
noncomputable def reductionRingEquiv (X Y : Type*) [CommRing X] [CommRing Y] (e : X ≃+* Y) :
    (X ⧸ nilradical X) ≃+* (Y ⧸ nilradical Y) :=
  e.quotientNilradical

/-! ### The base ring: two integral closures in one field -/

/-! ### The connector -/

section Connector

universe nA nC nK nM nT n₁ n₂ n₃ mA mC mK mM m₁ m₂ m₃

variable {A₁ : Type nA} {C₁ : Type nC} {K₁ : Type nK} {M₁ : Type nM} {K₂ : Type nT}
    [CommRing A₁] [CommRing C₁] [Field K₁] [Field M₁] [Field K₂]
    [IsDomain A₁] [IsDomain C₁] [IsDiscreteValuationRing A₁] [IsDiscreteValuationRing C₁]
    [Algebra A₁ C₁] [Algebra A₁ K₁] [Algebra A₁ M₁] [Algebra C₁ M₁]
    [Algebra K₁ M₁] [Algebra K₁ K₂] [Algebra A₁ K₂]
    [IsExtension A₁ C₁] [IsFractionRing A₁ K₁] [IsFractionRing C₁ M₁]
    [IsScalarTower A₁ C₁ M₁] [IsScalarTower A₁ K₁ M₁] [IsScalarTower A₁ K₁ K₂]
    [Module.Finite K₁ K₂]
    {A : Type mA} {C : Type mC} {K : Type mK} {M : Type mM}
    [CommRing A] [CommRing C] [Field K] [Field M]
    [IsDomain A] [IsDomain C] [IsDiscreteValuationRing A] [IsDiscreteValuationRing C]
    [Algebra A C] [Algebra A K] [Algebra A M] [Algebra C M]
    [Algebra K M] [Algebra K K₂] [Algebra A K₂]
    [IsExtension A C] [IsFractionRing A K] [IsFractionRing C M]
    [IsScalarTower A C M] [IsScalarTower A K M] [IsScalarTower A K K₂]
    [Module.Finite K K₂]

/-! ### The connector, taking the cancellation directly -/

end Connector

end Stacks.DiscreteValuationRing.EppLevelInduction

end
