# Positive opposite-Jacquet multiplicity for admissible quotients of induction

Author: Worker 165.

`Langlands.oppositeJacquetQuotientDetection` proves exactly the published
`Langlands.OppositeJacquetQuotientDetectionStatement.{uF,uV,uW}`. Its field,
inducing-carrier and quotient-carrier universes are independent. It retains
every prime, p-adic field, compatible topology, positive rank and block shape.
The inducing representation is irreducible and admissible; the quotient
representation is admissible and need not be irreducible.

This is an internal consequence of published second adjointness, algebraic
coinvariant surjectivity and actual finite-series multiplicity detection.
It introduces no new literature assertion or alternative formulation.

## Implemented proof

Write I for the actual normalized upper induction of sigma. Apply the standard
clause of `Langlands.Parabolic.normalizedSecondAdjointness` at the supplied
positive rank and block shape. With the given admissibility hypotheses it
provides a complex-linear equivalence

`Hom(I, P) ≃ Hom(sigma, oppositeJacquet P)`.

The image of the supplied nonzero intertwiner q is nonzero: a linear
equivalence sends zero to zero and is injective. The proof uses this
unconditional published second-adjointness theorem directly. No
second-adjointness statement or local Hom equivalence is assumed.

The existing `CuspidalJacquetMultiplicity.oppositeMap T B q` is an actual
intertwiner from the opposite Jacquet module of I onto that of P. Its
underlying linear map is the coinvariant map of q restricted to the actual
opposite unipotent subgroup.
`Langlands.coinvariants_map_surjective` proves it surjective from the
given surjectivity of q. This step needs no additional topology or
smoothness hypothesis.

Finally `jordanHolderQuotientSimpleMapDetection` applies to this surjection,
irreducibility of sigma, the supplied actual ambient count M and the nonzero
map from sigma obtained above. It returns an actual count m for the opposite
Jacquet module of P, with `0 < m` and `m <= M`. Its kernel short exact sequence
supplies the quotient's finite simple series from the ambient series; a
nonzero Hom alone does not supply that series.

The opposite Jacquet objects and map retain the actual opposite radical and
the inverse upper full modulus, transported through the existing product-Levi
equivalence. The induction retains its positive upper half-modulus covariance
and right translation.

## Scope and import audit

The direct project imports are the existing target statement,
`CuspidalJacquetFunctors`, `Jacquet.ExactProof`,
`Parabolic.SecondAdjointnessProof` and
`Filtration.SimpleMapMultiplicityDetectionProof`. They supply respectively
the exact target, the actual opposite quotient map, coinvariant surjectivity,
unconditional admissible second adjointness and actual-series quotient
multiplicity detection.

Recursively following project import lines at the Library base
`d8425b466384657b53f6106e0310f36fe92afff2` gives 250 existing project modules
besides this proof. Every imported Lean/Markdown pair matches that Library.
The closure consists of local-field and block-group constructions, Haar and
compact averaging results, smooth representations and contragredients, actual
induction and Jacquet functors, duality and adjointness, generic finite-series
algebra, and the existing support and character adapters.

In particular, second adjointness imports
`Exponents.UnitaryDualJacquetSupportAdapters` through
`Parabolic.SecondAdjointnessAssembly`. This brings in
`Exponents.DualJacquetStatement`, `Classification.OppositeJacquetReciprocity`,
`Classification.OppositeSupportJacquetAdapter`,
`Classification.TemperedSupportStatement` and
`Classification.TemperedInductionStatement`. The latter two define
propositions; their support, unitarity and induction conclusions are not
supplied or assumed by this proof. Their underlying analytic predicates and
transport constructions in `Classification.Tempered` and
`Classification.Essential` are also present. The other classification imports
are `ConstituentRelations`, `Supercuspidal`, `SupercuspidalTwist`,
`SupercuspidalContragredientStatement` and
`SupercuspidalContragredientAux`, in addition to the target and cuspidal
Jacquet object/functor modules. These provide definitions and general algebraic
or contragredient adapters, rather than an excluded classification conclusion.

No module for segment analytic classification, multisegment special-head
exhaustion, ordered special-head existence, quotient coverage, tempered block
uniqueness, square-integrable classification or exhaustion, or regular
exhaustion occurs in the transitive closure. The term uses only proved
second adjointness, the actual opposite quotient map, coinvariant
surjectivity and generic finite-series detection. It does not apply the
cuspidal multiplicity proposition defined in the imported object module.

The theorem neither constructs the supplied ambient count nor proves
admissibility of a particular segment, constructs a map between different
inductions, or constructs a segment constituent. It assumes no analytic
segment classification, special-head existence or exhaustion, quotient
coverage, tempered block uniqueness, square-integrable classification or
regular exhaustion result. The published statement pair and its imports are
unchanged.
