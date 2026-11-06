# The actual affine apartment splitting for supplied anisotropic data

This is a derived internal construction from the existing actual parahoric
zero datum and affine-apartment definitions. It assumes supplied
`ParahoricBuildingData G` for an anisotropic actual group. It does not assert
the existence of such data for an arbitrary connected reductive group.

The zero datum already includes an actual derived subgroup inclusion
`d : D → G` and a simply connected cover of it. The existing cover predicate
proves `IsDerivedSubgroup d` and that `D` is semisimple, hence affine and
smooth. The published existence of maximal split tori chooses an actual
maximal split torus `j : S' → D`.

Every split subtorus of an anisotropic group is trivial. Applying the
published homomorphism uniqueness theorem to `j` followed by the actual
closed inclusion `d` and to the original maximal split torus `S → G`
produces the unique mutually inverse maps `S' ≅ S`. The resulting map
`e : S' → S` is a closed immersion, and the diagram `j d = e i` commutes by
the same homomorphism uniqueness. The actual derived group and its inclusion
remain those supplied by the zero datum.

The identity of the trivial torus `S` is its zero endomorphism. Thus every
point is the identity, its embedding into `G` is central, and maximality of
the supplied split torus makes it the split component. Its cocharacter
lattice and real cocharacter space are zero. This proves the complement
condition for the ranges of `e` and the identity central-torus map. The
normalizer preserves `S'` via its identity automorphism; the apartment is a
subsingleton, so the centre acts trivially. The conjugation clause is the
existing general `hasAffineConjugations` theorem.

`anisotropicApartmentSplitting` chooses these actual splitting data, and
`satisfiesAffineApartmentAxiom_anisotropicApartmentSplitting` proves all
nine fields of the existing `SatisfiesAffineApartmentAxiom` predicate at
every universe `u`. This is precisely the supplied-data anisotropic case of
KP Axiom 4.1.4. It changes no quotient, action, root, centralizer, topology or
valuation normalization. General derived-subgroup and parahoric-data
existence and the other axiom families remain separate obligations.
