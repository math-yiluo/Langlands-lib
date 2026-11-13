# The actual smooth Aubert complex with published structural inputs

Internal construction by Worker 3640. This module instantiates the published
`RationalStandardComplex` on the actual rational points of a connected reductive
group over an arbitrary nonarchimedean local field. Its source motivation is
Aubert (1995), printed pp.2186–2187, and the official erratum (1996), printed
p.4687 display (*) and p.4690 Remark (1), display (**). It is a construction and
an assembly of intrinsic laws, rather than a proof of corrected exactness.

The ten `canonicalRational…` aliases retain the existing actual constructions.
All names below are in
`Langlands.Aubert.General.RationalPointFamily`, with prefix
`canonicalRational` on the left:

| Suffix | Published construction instantiated |
| --- | --- |
| `DegreeObject` | `rationalDegreeObject` |
| `Differential` | `rationalDifferential` |
| `Boundary` | `rationalBoundary` |
| `TerminalObject` | `Complex.terminalObject` on the same removed-root family |
| `TerminalProjection` | `rationalTerminalProjection` |
| `SharpObject` | `rationalSharpObject` |
| `SharpFunctor` | `rationalSharpFunctor` |
| `InitialMap` | `rationalInitialMap` |
| `InitialEquiv` | `rationalInitialEquiv` |
| `InitialDifferential` | `rationalInitialDifferential` |

The maps are the literal maps of `RationalStandardComplex`. The dependent
result types are obtained with `type_of%` from those same expressions.
`TerminalObject` uses `StandardComplex.removedFamily` on `parabolic`, `levi`
and `unipotent`, with the same semidirect decompositions, closedness,
unimodularity and inclusion proofs as the other aliases. At any degree it
is the quotient by the incoming image, without an exactness claim about the
outgoing map. The exterior coordinates use an arbitrary supplied
`LinearOrder` on the actual simple roots; this is not a canonical orientation.
The finite enumeration is obtained from the published `relativeRootSystem`
and `simpleRelativeRootFintype`, with no nonempty-root hypothesis.

The module supplies `standardCocharacter`, `standardParabolicOrder` and
`standardParabolicEndpoints` from their published proofs. Closedness is
`canonicalStandardUnipotent_isClosed`; compact exhaustion is
`standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement`,
which supplies unimodularity through the existing rational aliases. The
ambient topology is `pointTopology`. Affineness and smoothness follow from
connected reductivity; local compactness and the nonarchimedean group structure
are obtained from `rationalPoint_locallyCompactSpace` and
`Plancherel.rationalPoints_nonarchimedeanGroup`. These are constructed local
instances, not extra hypotheses of the aliases. No dynamic finite-length
preservation statement is an input.

The exported parameters, in order, are the local field and its instances,
the torus and group schemes, connected reductivity, the torus embedding,
the cocharacter, maximal splitness, genericity, the supplied root order,
and the smooth input and degree or root subset as appropriate. In particular
there is no extra affine, smoothness, point-topology, local-compactness,
nonarchimedean-group or root-enumeration parameter.

All constructions apply to every smooth complex representation in universe
`max (u + 1) v`, with arbitrary field universe `u` and independent module
universe `v`. The retained cokernel is taken at removed-root degree `|S|-|I|`,
so its coordinates have surviving subsets of cardinality `|I|`. The empty
simple-root set is included. The module asserts no vanishing of this quotient.

The five intrinsic theorems specialize published construction laws:
`canonicalRationalDifferential_square` uses `Complex.differential_square`,
`canonicalRationalInitialDifferential_square` uses
`Complex.initialDifferential_square`, and
`canonicalRationalTerminalProjection_comp_differential` uses
`Complex.terminalProjection_comp_differential`. The surjectivity and kernel
theorems use the corresponding `rationalTerminalProjection` laws. Thus the
terminal kernel is exactly its actual incoming image, without assuming
exactness at earlier degrees.

An inspection of all fifteen declarations finds only the standard axioms
`propext`, `Classical.choice` and `Quot.sound`. This is a dependency check on
the implemented construction, not an assertion that the remaining duality
proofs have no classification dependencies.

The support-category exactness theorem, corrected two-sided Bruhat filtration,
comparison of graded transition maps, associated-Levi Jacquet comparison,
finite-length specialization, Sharp irreducibility and double-Sharp results
remain separate proof obligations. No statement target or proof owned by
another task is changed here. The imported operator module contains conditional
finite-length constructions, but none of those conditional declarations is
called by this module's constructions or intrinsic laws. No classification
independence conclusion about the remaining representation-theoretic results
is asserted.
