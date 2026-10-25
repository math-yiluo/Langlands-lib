# Restriction and arithmetic transport for the prime-break comparison

Author: Worker 32.

This derived support module constructs the actual restriction homomorphism and
collects elementary transport facts used by the pending proof of
`Langlands.LocalClassField.PrimeBreakUnramifiedBaseChange`. It does not prove that
proposition or compare the lower ramification groups. All declarations are in
`Langlands.LocalClassField`.

`primeBreakRestriction` takes intermediate fields E, K, and M over a field k,
inclusions E ≤ M and K ≤ M, and normality of E/k. With the algebras induced by
these inclusions, it maps Gal(M/K) to Gal(E/k) by first restricting scalars to k
and then applying Mathlib's normal restriction. The construction uses the actual
field maps. `primeBreakRestriction_commutes` proves that restriction commutes
with E → M using `AlgEquiv.restrictNormal_commutes`.

`primeBreakRestriction_injective` adds M = E ⊔ K. An element in the kernel fixes
the restricted copy of E, by the commutation identity, and fixes the restricted
copy of K because it is a K-automorphism. Mathlib's fixing-subgroup formula for a
supremum and the equality of that supremum with the top intermediate field force
the element to be the identity. No linear disjointness or Galoisness of K/k is
assumed. This lemma proves injectivity, not surjectivity.

`primeBreakRestriction_displacement` is an algebraic transport identity. For
arbitrary integer-valued functions νE and νM with νM(inclusion z) = νE(z), it
identifies the tests “displacement equals zero or has order at least n” for an
element π and its image. The proof rewrites the displacement with preservation
of subtraction and the commutation identity, and uses injectivity of the field
inclusion for the zero alternative. Keeping that alternative is necessary when
the functions are the Library's normalized orders, which assign order zero to
zero. The lemma quantifies arbitrary integer thresholds.

`primeBreakResidueMap_surjective_of_total` treats independent universes and the
canonical topological data of supplied p-adic field packages F and E, with their
supplied compatible algebra. From e(E) = [E:F] e(F), the published identity
`PadicField.ramificationIndex_mul_extensionResidueDegree` and positivity of e(E)
give relative residue degree one. The published residue cardinality formula then
shows the two residue fields have equal finite cardinality. The actual relative
residue map is injective as a field homomorphism, hence surjective. The supplied
algebra is identified with the algebra induced by its own algebra map; no
alternative extension map is substituted.

`primeBreakCompositumData` imports and applies the published
`totalUnramifiedCompositum`. Its hypotheses are total ramification of E/F,
unramifiedness of K'/F, Galoisness of E/F, and any presentation M of E ⊔ K' with
any supplied inclusion proofs. The theorem returns surjectivity of the actual
relative residue map for M/K' and preservation of the canonical order of every
element under E → M. The proof identifies the existential compositum witness
with the given finite-intermediate-field package using subtype extensionality.
Proof irrelevance identifies the finiteness certificates and inclusion proofs.
It then projects the two conclusions of `totalUnramifiedCompositum`. This handles
all presentations and does not impose a Galois assumption on K'/F.

These are internal consequences of published Library arithmetic and Mathlib
field theory. Their mathematical background is Serre, *Local Fields* (1979),
V.4, printed pages 87–88; the restriction construction is an implementation
choice. The registered 2019 author errata, PDF pages 2–3, contains no correction
to that passage. The module does not use a uniformizer criterion or assume a
comparison of ramification filtrations. The naming reflects its intended
consumer; no prime-degree assumption is needed for these support results.
