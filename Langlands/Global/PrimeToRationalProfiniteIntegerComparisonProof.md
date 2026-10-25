# Normalized away rational residue and finite-adele comparisons

Author: Worker 315.

The theorem `Langlands.Global.primeToRationalProfiniteIntegerAdeleComparisons`
proves exactly the published proposition
`Langlands.Global.PrimeToRationalProfiniteIntegerAdeleComparisons`, with no
outer parameters or additional hypotheses. The proposition quantifies over
an explicit full comparison `h : RationalProfiniteIntegerAdeleComparison`
and every natural modulus `m`. The proof uses exactly the coupled full
witnesses `h.choose` and `h.choose_spec.2.2.2.choose`.

This is an internal algebraic derivation using the published scalar rings,
their restriction maps, Worker 18's published integral comparison theorem
`primeToIntegralProfiniteIntegerAdeleComparisons`, and Mathlib's flatness and
localization theorems. The integral theorem is imported by name; no part of
its construction is repeated here. The argument below proves the rational
assembly and asserts no additional result from external literature.

## Integral input and rational lift

The private helper `awayComparisons_of_integral` applies the integral
comparison proposition to `h.choose`, its two continuity proofs, and its
integer normalization. For each `m` this supplies a ring equivalence `e₀`
from the actual inverse limit `PrimeToProfiniteIntegerRing m` to the
published integral subring `primeToIntegralFiniteAdeles m`, with both
continuities, integer normalization, and restriction compatibility with
that same full integral witness. The closing theorem supplies the published
proof of the integral proposition to this helper.

For any commutative ring `R`, rational algebra `A`, and ring homomorphism
`f : R →+* A`, `rationalLift f` uses `Algebra.TensorProduct.lift` to construct

```text
ℚ ⊗[ℤ] R →ₐ[ℚ] A,     q ⊗ a ↦ algebraMap ℚ A q * f a.
```

The two defining maps commute because `A` is commutative. In the application,
`f` is `e₀` followed by the inclusion of the integral away adeles into
`PrimeToFiniteAdeles m`. Thus the required rational pure-tensor formula is
true by construction.

## Injectivity

The private lemma `rationalLift_injective` assumes only injectivity of `f`.
Mathlib's `IsLocalization.flat` makes `ℚ` flat over `ℤ`, since it is the
localization at the non-zero-divisors. Consequently
`Module.Flat.lTensor_preserves_injective_linearMap` makes the base change
of the integer-linear map underlying `f` injective.

For the rational algebra `A`, `IsLocalization.moduleLid` identifies
`ℚ ⊗[ℤ] A` with `A`. The proof checks on pure tensors that the linear map
underlying `rationalLift f` is this equivalence composed with the base
change of `f`. Their composite is injective. In the application, injectivity
of `f` follows from injectivity of `e₀` and of the subring inclusion.
No nontriviality assumption on either ring is needed.

## Restriction and surjectivity

The private lemma `finiteRestriction_surjective` lifts an arbitrary away
finite adele by assigning its given coordinate at each retained finite
place and zero at every omitted place. Its nonintegral places form a subset
of the image of the original finite exceptional set under the subtype
inclusion, and hence are finite. This produces an element of the actual
full restricted product. Restricting it back recovers the original adele
coordinatewise.

In `awayComparison_of_integral`, let `g` be the rational lift and let `r`
be the tensor map induced by the identity on `ℚ` and residue restriction.
Tensor induction proves the commutative square for every full tensor `x`:

```text
g (r x) = primeToFiniteRestriction m (h.choose_spec.2.2.2.choose x).
```

On pure tensors the equation follows from the integral restriction identity,
the chosen full rational witness's pure-tensor formula, and preservation of
rational scalars and multiplication by finite restriction. Additivity
extends the equation to all tensors.

To obtain a preimage of an away adele `a`, first choose a full finite adele
`b` restricting to `a`. Apply the inverse of the specified full rational
equivalence to `b`, then apply `r`. The square shows that the resulting
tensor maps to `a`, proving surjectivity of `g`. This argument does not
assume surjectivity of residue restriction.

`AlgEquiv.ofBijective` turns `g` into the required rational algebra
equivalence with the same forward map. The final tuple includes the
integral properties already supplied, the defining pure-tensor formula,
and the restriction square specialized to pure tensors.

## Scope

The proof works for every natural `m`, including zero and one. At zero the
away rings are trivial and no finite place is retained; the zero-extension
and flatness arguments still apply. At one all finite places are retained.
The proof adds no positivity, primality, nontriviality, or comparison
hypothesis. Its full comparison is precisely the explicit hypothesis
already quantified by the target.

Both integral continuities concern the existing topologies. The rational
comparison is algebraic: no topology on the tensor product or continuity
of the rational equivalence is asserted. All helper declarations are
private, and the target statement and its imports are unchanged.
