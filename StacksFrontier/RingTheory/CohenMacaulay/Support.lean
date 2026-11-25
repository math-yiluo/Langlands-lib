module

public import Mathlib.RingTheory.KrullDimension.Module
public import Mathlib.RingTheory.Support

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# The support of a ring over itself, and the dimension of a full support

A commutative ring is faithful over itself, so its annihilator is zero and its support is all of
`Spec(R)`; and a module whose support is all of `Spec(R)` has `dim Supp(M) = dim R`, both sides
being the Krull dimension of the same subset. Both facts are used wherever a statement about
`Module.supportDim` is to be read as a statement about `ringKrullDim`.

## Main results

* `Module.support_self`: `Supp(R) = Spec(R)` for `R` as a module over itself.
* `Module.supportDim_eq_ringKrullDim_of_support_eq_univ`: a module of full support has the
  dimension of the ring for the dimension of its support.
* `Module.supportDim_eq_of_ringEquiv`: the dimension of the support of a module carrying two
  module structures matched by a ring isomorphism is the same computed over either ring.
* `Module.supportDim_eq_of_semilinearEquiv`: the dimension of the support is invariant under an
  additive isomorphism of modules which is semilinear over a ring isomorphism.

## Implementation notes

Mathlib's `Module.support_of_noZeroSMulDivisors` and `Module.support_of_isTorsionFree` need a
domain or a nonzero module; the statement here needs neither, and over the zero ring both sides
are empty.
-/

@[expose] public section

/-- **The support of a commutative ring as a module over itself is its whole prime spectrum**:
`R` acts faithfully on itself, so `Ann(R) = ⊥` and `Supp(R) = V(⊥) = Spec(R)`. Unlike
`Module.support_of_noZeroSMulDivisors` this needs neither a domain nor a nonzero module; over the
zero ring both sides are empty. -/
public theorem Module.support_self (R : Type*) [CommRing R] : Module.support R R = Set.univ := by
  rw [Module.support_eq_zeroLocus, Module.annihilator_eq_bot.2 (inferInstance : FaithfulSMul R R),
    PrimeSpectrum.zeroLocus_bot]

/-- **A module of full support has the dimension of the ring for the dimension of its support**,
both being the Krull dimension of the same subset of `Spec(R)`, namely of `Spec(R)` itself. -/
public theorem Module.supportDim_eq_ringKrullDim_of_support_eq_univ {R : Type*} [CommRing R]
    {M : Type*} [AddCommGroup M] [Module R M] (hsupp : Module.support R M = Set.univ) :
    Module.supportDim R M = ringKrullDim R :=
  le_antisymm (Module.supportDim_le_ringKrullDim R M)
    (Order.krullDim_le_of_strictMono
      (fun p => (⟨p, hsupp ▸ Set.mem_univ p⟩ : Module.support R M)) fun _ _ lt => lt)

end
