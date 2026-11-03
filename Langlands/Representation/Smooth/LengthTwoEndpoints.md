# Object-level deductions for a rank-one Jacquet pattern

Author: Worker 64. Internal generic algebra supporting task
`1244dad8-89c0-4c13-95f7-1942ccf77842`.
All public declarations are in `Langlands.SmoothRep`.
The coefficient field, group and representation-carrier universes `uR`, `uG`
and `uV` are independent. The group has an arbitrary topology; no compatibility
with multiplication is needed for these algebraic deductions.

The construction `endpointIsomorphismsOfShortExactTwoIrreducibles` takes two
actual short exact sequences with the same middle object,
`A → E → B` and `σ → E → τ`. It assumes that `σ` and `τ` are irreducible
and the carriers of `A` and `B` are nontrivial. It returns actual categorical
isomorphisms in one of the two orders:
`((A ≅ σ) × (B ≅ τ)) ⊕ ((A ≅ τ) × (B ≅ σ))`.
The construction chooses witnesses from the proved proposition
`endpoints_iso_of_shortExact_two_irreducibles`.
The supplied simple objects may be isomorphic, and the sequences need not split.
Finite length of any object is derived rather than assumed.

The proof first obtains length two for `E` from the second sequence.
`isIrreducible_endpoints_of_shortExact_length_two` uses actual length additivity
and positivity for the first sequence: two positive extended natural numbers
whose sum is two are both one. The endpoint objects are consequently
irreducible. Their finite length follows from irreducibility; that of `E`
follows from its computed length.

Canonical composition-factor sums for the two actual sequences now give
`[A] + [B] = [σ] + [τ]` in the integral lattice on genuine irreducible
isomorphism classes. The private basis calculation evaluates at `[A]` to
show that `[A]` equals `[σ]` or `[τ]`, then cancels the matching summand.
Equality of genuine irreducible labels gives actual smooth-category
isomorphisms. The calculation uses the canonical factor sums of actual
objects and their actual exact sequences.

`isZero_iff_subsingleton_carrier` identifies the categorical zero-object
condition with the subsingleton condition on the actual carrier: a zero object's
identity equals its zero morphism, and conversely the subsingleton carrier makes
those maps equal. `isZero_endpoints_of_shortExact` uses the actual injection
and surjection to propagate a zero middle object to both endpoint objects.

The declaration-level dependencies used in the implemented argument are:

- `Langlands.repLength_eq_add_of_exact`, `repLength_pos_iff` and
  `repLength_eq_one_iff`, from
  [`RepresentationLength`](../Filtration/RepresentationLength.md).
- `Langlands.SmoothRep.hasFiniteLength_of_isIrreducible` and
  `irreducibleIsoClass_eq_iff`, from
  [`IrreducibleRealization`](IrreducibleRealization.md).
- `Langlands.SmoothRep.IrreducibleGrothendieckProof.compositionFactors_shortExact`
  and `compositionFactors_irreducible`, from
  [`IrreducibleCompositionFactors`](IrreducibleCompositionFactors.md).
  These use the published actual composition-series existence,
  Jordan–Hölder independence and short exact multiplicity additivity.
- Mathlib's `Module.length_ne_top_iff`, `Finsupp.single_left_injective`,
  additive cancellation, and `CategoryTheory.Limits.IsZero.iff_id_eq_zero`.
  The zero-object proof also uses the faithful inclusion
  `Langlands.SmoothRep.toRep` and `Rep.hom_ext`.

The provenance is internal algebra derived from the imported actual
representation, module-length and composition-series constructions. No
numbered literature assertion is transcribed. The proof uses no Langlands
classification, character independence, geometric lemma, adjointness or
cuspidal-support theorem.

This unit supplies generic deductions with explicit local premises. It does
not establish the required actual Jacquet exact sequences, their nonzero
endpoints, or the representation-theoretic inputs of
`RationalRankOneJacquetModulesStatement`, and does not prove that full target.
