# Normalized comparison of the profinite-integer constructions

`Langlands.Global.profiniteIntegerCompletionComparison` proves exactly the
published proposition `Langlands.Global.ProfiniteIntegerCompletionComparison`.
It has no parameters or additional hypotheses. The resulting equivalence is

```lean
Multiplicative Langlands.Global.ProfiniteIntegerRing ≃*
  Langlands.Weil.ProfiniteIntegers
```

Both the equivalence and its inverse are continuous, and for every integer `z`
it sends the residue family of `z` to
`Langlands.Weil.frobenius (Multiplicative.ofAdd z)`.

## Implemented proof

The density lemma `Langlands.Global.residue_integer_dense` is public for reuse
by the [integral away comparison](PrimeToIntegralProfiniteIntegerComparisonProof.md).
The remaining auxiliary declarations are private to this proof module.

1. **Density of integers in the residue ring.** An open neighborhood in the
   subspace topology contains a product neighborhood restricting only finitely
   many positive moduli. Take their product `m`, with empty product equal to
   one. Choose an integer representing the given compatible family's coordinate
   at `m`. Since each selected modulus divides `m`, compatibility makes the
   integer's residue agree with the family at every selected coordinate. Thus
   the canonical integer residue map has dense range.

2. **The map from the existing completion.** Write scalar addition
   multiplicatively and form `integerHom` from the integer ring homomorphism.
   Apply Mathlib's `ProfiniteCompletion.lift` to the profinite group
   `ProfiniteGrp.of (Multiplicative ProfiniteIntegerRing)`. The published compact,
   Hausdorff and totally disconnected topology supplies this profinite group;
   no topology is replaced. The result `completionToResidues` is a continuous
   group homomorphism from the existing Weil completion. Mathlib's `lift_eta`
   proves that it sends each canonical Frobenius integer to its residue family.

3. **Factorization of every finite integer quotient.** For a homomorphism from
   `Multiplicative ℤ` to a finite group `H`, let `n` be the positive cardinality
   of `Additive H`. The corresponding additive homomorphism kills `n`, since
   `n` times every element of that finite additive group is zero. `ZMod.lift`
   therefore factors it through `ZMod n`; changing back to multiplicative
   notation gives a factorization with the exact integer normalization. This
   argument does not require `H` to be commutative.

4. **Injectivity.** Each coordinate of the actual Weil completion is a finite
   quotient of the integer group. Apply the preceding factorization to that
   quotient map. Its continuous extension obtained by composing
   `completionToResidues`, reduction modulo `n`, and the finite factor map
   agrees with the completion's coordinate projection on integers. Mathlib's
   `ProfiniteCompletion.denseRange`, and Hausdorffness of the finite quotient,
   imply that the two continuous maps agree everywhere. Consequently equal
   residue images imply equality at every finite-quotient coordinate, hence
   equality in the completion.

5. **Surjectivity and inversion.** The image of `completionToResidues` contains
   every integer residue family, hence is dense by step 1. It is compact and
   therefore closed in the Hausdorff residue ring, so it is the whole ring.
   Turn this bijective homomorphism into a multiplicative equivalence and take
   its inverse for the direction requested by the statement. The inverse is
   continuous by the compact-to-Hausdorff continuous-bijection theorem.
   Applying the forward equivalence to the required integer equality reduces
   it directly to `completionToResidues_integer`.

## Normalization, provenance, and scope

The source operation is scalar addition. Its group identity is scalar zero.
The normalization holds for every positive, zero, and negative integer, so it
also fixes the sign of the comparison. In particular scalar one maps to the
canonical integer-one Frobenius element.

This is an internal proof comparing the two concrete published constructions,
not a theorem attributed verbatim to an external source. The residue ring and
its source motivation are documented in
[`ProfiniteIntegerRing.md`](ProfiniteIntegerRing.md); the exact comparison target
and its conventions are documented in
[`ProfiniteIntegerCompletionComparison.md`](ProfiniteIntegerCompletionComparison.md).
The density argument specializes the finite-coordinate neighborhood method also
used for Mathlib's completion density theorem. The finite-quotient argument uses
Mathlib's `ZMod.lift`, `card_nsmul_eq_zero'`, and the completion's actual quotient
coordinates. These APIs are in `Mathlib/Data/ZMod/Basic.lean`,
`Mathlib/GroupTheory/OrderOfElement.lean`, and
`Mathlib/Topology/Algebra/Category/ProfiniteGrp/Completion.lean`, at the project
pin `5ed2965256430c3649e86755f9576b54eca72435`.

The proof imports the unchanged published statement and preserves its two
objects, canonical integer maps, and topologies. It uses no assumed comparison,
replacement completion, p-adic product, or finite-adele identification. It does
not assert a ring equivalence or equip the Weil group completion with a ring
structure. Worker 18 authored this proof and explanation.
