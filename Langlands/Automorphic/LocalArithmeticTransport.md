# Arithmetic transport of irreducible local components

The lemmas compare the local factors of supplied arithmetically conjugate cuspidal realizations. They use the full operator representations and the actual inclusions of the local groups into the finite adeles. They supply the local stabilizer comparison for the use of Henniart–Herb (1995), Proposition 5.5, in Harris (1998), Proposition 4.8.

`finiteEquiv_localInclusion` checks each local projection of a matrix supported at one place. At the corresponding place the projection is its entrywise transport. At each other place it is the identity. `finiteEquiv_localInclusion_of_extends` identifies a continuous extension of the field isomorphism with the completion map by agreement on the dense image of the number field.

`nonempty_localComponent_equiv_of_arithmeticTransport` composes the source's local subspace inclusion with the arithmetic transport equivalence of full spaces. The transport equation and compatibility of local inclusions make the composition an intertwiner for the inverse pullback. The pullback is irreducible. Its embedding and the target component's embedding into the target full realization give the local equivalence by `nonempty_local_equiv_of_injective`.

At a unique place, `nonempty_localComponent_equiv_of_galoisConjugate` uses the extended global automorphism on the completion. It is continuous as a linear map between finite-dimensional spaces over the completed base. `hasTrivialGaloisStabilizer_of_distinct_conjugates` expresses the inverse of a nonidentity local automorphism as a bounded global generator power, so inverse pullback for this power is pullback by the original local automorphism. A local stabilizer would make the supplied conjugate factor equivalent to the original, contradicting inequality of their smooth classes.

`not_isGaloisStable_of_localComponent_isoClass_ne` gives global regularity directly. Stability would identify the two full classes by uniqueness of arithmetic transport. Transporting the presentation along that equivalence and applying uniqueness of irreducible local components would identify their smooth classes.

The local-inclusion identity for finite adelic transport comes from `FiniteLocalCMTransport`.
