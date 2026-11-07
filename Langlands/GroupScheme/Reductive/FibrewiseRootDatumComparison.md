# Compare common coordinate root data on one field fibre

This internal construction compares two supplied full fibrewise coordinate root data by an isomorphism on one actual field-valued fibre. The commutative base ring is arbitrary. The two finite coordinate types may differ; both root-index types and all base objects lie in the arbitrary universe `u`.

Assume `IsFibrewiseRootDatumOf I G i P` and `IsFibrewiseRootDatumOf I' H j Q`. Supply a field `k` with its original `R`-algebra structure, connected reductivity of both actual `k`-base changes, maximality of the canonical coordinate versions of the two actual torus maps on that fibre, and an actual isomorphism between the two base-changed groups. The theorem `IsFibrewiseRootDatumOf.nonempty_equiv_of_fieldIso` produces `Nonempty (RootPairing.Equiv P Q)`. The definition `equivOfFieldIso` chooses such a full equivalence. Neither result requires the supplied group isomorphism to preserve the chosen tori.

The proof specializes each fibrewise predicate to `k`. The published arbitrary-field comparison `nonempty_rootDatumEquiv_of_iso` then gives an equivalence of the two actual realized root data. Composing with the full realization equivalences, using `CoordinateRootDatum.equivOfFieldRealizationEquiv`, gives an equivalence of the original coordinate data. The maps preserve the whole lattices and both root embeddings, with Mathlib's contravariant convention on cocharacters; central lattice directions are retained.

The helper `nonempty_equiv_of_reductive_fieldIso` obtains the two connected-reductivity hypotheses from global reductivity using the published actual-field-fibre theorem. It still requires maximality on the supplied fibre. No local-ring, domain, fraction-field, or algebraic-closedness hypothesis is used in this unit.

The construction uses only published field comparison and reductive base change, and the full fibrewise coordinate-datum interface. It does not construct a common datum, prove coroot constancy, establish maximality on an arbitrary fibre, or apply an integral isomorphism theorem. Those remain separate obligations in the proof of the strict-Henselian generic-isomorphism statement.
