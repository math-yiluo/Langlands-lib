# Full coordinate root data on every field-valued fibre

This internal interface defines a common full root datum for an actual coordinate split-torus map over a commutative ring. The base ring need not be a domain or a local ring.

For a finite coordinate type `I`, a Mathlib root datum `P` has its two lattices equal to the entire groups `I → ℤ`. `CoordinateRootDatum.fieldRealization k P` transports it to the actual character and cocharacter lattices of the coordinate split torus over a supplied field `k`, using the inverses of the published integral coordinate equivalences. Both roots and coroots become the corresponding actual fixed-exponent homomorphisms. The pairing evaluated on fixed-exponent characters and cocharacters is the original pairing of `P`.

`CoordinateRootDatum.fieldRealizationEquiv k P` is the full root-pairing equivalence supplied by the published general transport construction `SplitExistence.rootPairingMapEquiv`. Its weight map sends an exponent vector to its actual character, and its contravariant coweight map takes an actual cocharacter to its exponent vector. `equivOfFieldRealizationEquiv` composes this equivalence and its inverse with an equivalence of two realized data. Thus all lattice directions, including central directions, are retained.

For an actual affine group scheme `G` over `Spec R` and an actual map `i` from the coordinate split torus, `IsFibrewiseRootDatumOf I G i P` asserts:

- the root-index type of `P` is finite;
- `P` is reduced;
- for every supplied field `k` in the base universe, every field structure, and every `R`-algebra structure on `k`, the realization of `P` satisfies the published actual predicate `IsRootDatumOf` for the canonical coordinate version of the actual `k`-base change of `i`.

The last condition uses the original algebra structure of each supplied field. `IsRootDatumOf` requires the actual lattice pairing, the actual roots defined by nonzero adjoint weight spaces, and a normalizing rational point realizing every reflection on the entire character lattice. It therefore constrains coroots as well as root support. The definition adds no reductivity, maximality, smoothness, closedness, connectedness, or domain assumption; those geometric hypotheses belong to separate existence and classification statements.

The `field` helper specializes this condition to any supplied field algebra. The `pairing` helper shows that the coordinate pairing is the standard integer dot product whenever such a field is supplied, by comparing with the actual lattice pairing. The `mem_roots_iff` helper identifies the actual root characters on that field fibre with the roots of `P` in common integral coordinates. The two other helpers extract finiteness and reducedness.

All constructions are derived from published lattice coordinate equivalences, actual exponent characters and cocharacters, the canonical coordinate split-torus base-change map, the actual root-datum predicate, and the general full-datum transport equivalence. No new external structural assertion is used.

This interface does not establish existence of a common full datum, constancy of coroots in a reductive family, or the integral isomorphism theorem. In particular, root-support constancy alone is not asserted to provide this predicate. Those structural obligations remain necessary for the strict-Henselian generic-isomorphism theorem.
