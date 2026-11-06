# A simultaneous standard presentation of an actual dynamic triple

Author: Worker 1212.

This internal construction chooses a maximal split torus, a generic direction
and a finite actual-simple-root index for an arbitrary cocharacter of a connected
reductive group over a field. It retains `StandardCocharacterStatement` as an
explicit structural input. The output identifies all three standard subgroup
functors with the original dynamic parabolic, centralizer and unipotent subgroup
functors on every test scheme. It also retains the original cocharacter's
factorization through the chosen torus.

`DynamicStandardPresentation` stores this data, and
`dynamicStandardPresentation` chooses it. The field and group scheme share an
arbitrary universe `u`; no local-field or characteristic restriction is used.

The construction uses the published `cocharacterMaximalSplitTorus` factorization
and `IsSplitTorus.exists_genericCocharacter_refining` refinement. The latter makes nonnegative root pairings for the generic direction
imply nonnegative pairings for the original cocharacter. The selected finite
index consists of the actual simple roots whose original pairing is zero. The
original cocharacter is standard for that face, so the supplied standard
cocharacter statement gives the three simultaneous equalities. The proof first
constructs a `Nonempty` witness in `Prop`, then uses `Classical.choice` to select
the presentation. Finiteness comes from
`simpleRelativeRootFintypeOfIsSplitTorus`, not a retained root-system premise.

This is derived presentation data. It does not prove the retained structural
statement, a representation-theoretic comparison or a finite-length theorem.
