# Exact K0 of rational standard Jacquet restriction in stages

This internal adapter defines `standardIteratedJacquetK0` for the actual
standard rational-point subgroups and proves that it equals direct
restriction in `standardJacquetK0_stages_of_modulus`. Restriction first to the Levi
indexed by `J`, then inside that Levi to the literal restricted subgroup
indexed by `I : Finset J`, agrees on exact finite-length K0 with direct
restriction to `leviIndex J I`. The final pullback along the inverse of
`subgroupOfContinuousEquiv` identifies the nested descendant with the actual
ambient subgroup `levi i ν (leviIndex J I)`.

The field and representation universes `u` and `v` are independent.
Representation carriers have universe `max (u + 1) v`. The field has an
arbitrary topology; the affine ambient group's rational points carry
`pointTopology` and are assumed locally compact and nonarchimedean. The
connected reductive group, maximal split torus and generic cocharacter are
explicit. The named `StandardCocharacterStatement` and
`StandardLeviIntersectionStatement` supply the actual decompositions and
inclusions. Closedness of every ambient radical and of the coarse Levi is
assumed. No finite root enumeration or restriction on characteristic is used.

The theorem retains the published stages interface's two further inputs:
the restricted inner radical is a limit of compact subgroups, and the
product of the actual coarse and inner positive Haar characters equals the
fine positive Haar character. The latter is exactly the displayed premise
`hδ`, expressed using `standardInnerJacquetModulus`. This unit does not prove
that Haar factorization. Finite-length preservation and preservation of
actual finite-length short exact sequences are explicit for all ambient
Jacquet functors and for the one inner Jacquet functor. It does not assume
the desired K0 identity or a representation transitivity statement.

The proof uses `FiniteLengthGrothendieckGroup.hom_ext_object` to reduce
equality of maps to their values on actual finite-length representations.
The definitions of `jacquetK0` and exact pullback and
`FiniteLengthGrothendieckGroup.map_ofObject` compute both sides. The
component of the published `standardJacquetStagesIso` is an isomorphism
between those actual smooth representations. Applying
`FiniteLengthGrothendieckGroup.ofObject_eq_of_iso` proves equality of their
classes, with all actual short exact sequence relations retained.

The provenance is internal and derived from `RationalJacquetStages`,
`AlternatingOperator`, `FiniteLengthGrothendieckFunctor` and
`FiniteLengthGrothendieckTransport`. At the proof-body level the
representation comparison is `standardJacquetStagesIso`, whose
`normalizedJacquetStagesIso` proof uses the actual localization tower
`TowerDatum.twistedEquivOfEq` and the compact-limit triviality of the
coarse positive character on the inner radical. Exact pullback preservation
uses `SmoothRep.pullbackFunctor_preservesFiniteLength`, proved using
`FiniteLengthAssembly.finiteLength_comp_surjective_iff` and its elementary
invariant-subspace comparison; it does not invoke a Langlands
classification theorem. These are declaration-level dependencies, not a
claim about the full imported-module closure. This adapter makes no use of
character independence, adjointness, the geometric lemma or cuspidal
support classification. The whole rational Aubert Jacquet identity,
common geometric-term reduction and longest-survivor comparison remain
separate obligations.
