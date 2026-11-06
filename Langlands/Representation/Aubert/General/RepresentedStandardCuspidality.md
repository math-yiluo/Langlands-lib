# From represented-parabolic vanishing to standard cuspidality

Author: Worker 1276.
Worker 1742 specified the consumer interface.

This internal adapter constructs the canonical linear equivalence
`standardUnipotentCoinvariantsEquiv` between the coinvariants of a represented
standard radical and those of the exact standard point subgroup. It preserves
the class of each original vector. Equality of the radical point images gives
equality of the relation submodules, and `Submodule.quotEquivOfEq` supplies the
linear equivalence. This construction needs only the field, affine ambient
group scheme, torus morphism, cocharacter, finite face, canonical point topology,
and smooth representation; it has no geometric-recognition, local compactness
or root-system premise.

The vanishing theorem uses this equivalence to compare the existing
represented-parabolic and standard point-subgroup definitions of Jacquet
vanishing. It retains the universal
`ParabolicDynamicStatement` and `StandardCocharacterStatement` as explicit
premises. It does not prove those statements or the full
coefficient-compactness proposition.

The geometric recognition argument assumes that the ambient group scheme `G`
is connected reductive. The proof uses the published closed representatives of
the exact choice-free standard subgroup functors. A standard cocharacter
identifies those functors with the three corresponding dynamic subgroups on
every test scheme.
The parabolic-dynamic premise recognizes the parabolic representative.
The published dynamic-centralizer reductivity and dynamic geometric-radical
proofs recognize the Levi and the matching geometric unipotent radical.
The published preservation of unipotence under field extension supplies the
comparison with the Levi interface, which requires the unipotent radical both
over the ground field and after base change to its algebraic closure.
The existing represented dynamic multiplication theorem supplies the required
Levi-first multiplication isomorphism.

For a proper finite face, a missing actual simple root pairs positively with
the standard cocharacter. Its negative is an actual root by the supplied
relative-root-system realization. The published `RootParabolicProper` proof
constructs a dual-number point excluded from that dynamic parabolic, proving
properness of its all-test functor. An isomorphism of the representative with
the ambient group would make this functor the whole group, a contradiction.
This step does not require a nonidentity rational root point or the separate
standard-parabolic order statement.

The assumed vanishing of all proper actual represented-parabolic normalized
Jacquet modules now applies to these representatives. Their radical point
image is literally the existing standard unipotent subgroup. Both normalized
Jacquet constructions use localization quotients by that subgroup; the
normalization changes the action but not the carrier. The surjectivity of the
constructed linear equivalence transfers subsingletonness to each standard
Jacquet module.

The result has independent field and representation-carrier universes. It
requires a connected reductive ambient group scheme `G` over a field `k` with
Hausdorff topology (`T2Space k`), the exact canonical point topology, local
compactness, the nonarchimedean group structure, a maximal split torus and
generic cocharacter, a relative-root-system realization, a finite enumeration
of actual simple roots, and closedness of the standard unipotent subgroups. No irreducibility,
admissibility, finite dimension, finite length, or central character is used.
The provenance is internal composition of the published interfaces and proofs
named in the imports; no new assertion from the literature is claimed.
