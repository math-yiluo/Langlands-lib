# Ambient normalization of both endpoints of the actual geometric term

This internal construction combines the published source and target
normalization adapters for the literal intersections of `GeometricK0Target`.
Its provenance is those published definitions and their proved comparisons
of each radical in two ambient groups. It asserts no new literature theorem.

For arbitrary subgroup families `P`, `M`, `U`, subsets `I`, `J`, and element
`n`, `geometricTermAmbientFunctor` is the actual source ambient Jacquet
functor, followed by the published conjugation functor, followed by the
actual target ambient induction functor. The source parabolic, Levi and
radical are respectively
`M J ∩ n⁻¹ (P I) n`, `M J ∩ n⁻¹ (M I) n`, and
`M J ∩ n⁻¹ (U I) n`. The target intersections are
`M I ∩ n (P J) n⁻¹`, `M I ∩ n (M J) n⁻¹`, and
`M I ∩ n (U J) n⁻¹`. The supplied `hs` and `ht` remain their actual
semidirect decompositions inside `M J` and `M I`.

The source functor performs actual trivial-character localization by its
radical restricted to `M J`, transports the output along the inverse
subgroup identification, and twists by that radical's ambient inverse
half-Haar character. The target functor transports the input to its inside
Levi, inflates along the supplied actual projection, twists by its own
radical's ambient positive half-Haar character on the entire inside target
parabolic, and takes raw smooth induction to `M I`. In particular, the
positive twist stays after inflation. Each required ambient normalizer
inclusion is already derived in the endpoint modules from the corresponding
decomposition and literal intersection containments. Closedness uses the
existing hypotheses on `M` and `U`. The conjugation action remains
`σ(n⁻¹ x n)`.

`geometricTermSourceAmbientFunctor_eq_ambient` unfolds the two composites
and substitutes `geometricTargetInductionFunctor_eq_ambient`. This is an
equality of actual functors. `geometricTermAmbientIso` composes the published
`geometricTermSourceAmbientIso` with `eqToIso` of that equality. Thus the
comparison with the original actual geometric term is a natural
isomorphism; no equality of the source functors is asserted.

`geometricTermAmbient_hasFiniteLength` takes the finite-length witness from
`geometricTerm_hasFiniteLength` and transports it along the component of
`geometricTermAmbientIso` using `SmoothRep.hasFiniteLength_of_iso`. Its only
term-preservation premise is the existing `GeometricTermFiniteLength`,
with its four actual source and target preservation conditions.

`geometricTermK0_ofAmbient` first rewrites by
`geometricTermK0_ofRepresentation`, then applies
`FiniteLengthGrothendieckGroup.ofObject_eq_of_iso` to the same component.
It identifies the published integer-linear term map on every actual
finite-length representation class with the class of the composite just
constructed. The output length witness is derived above. The exact
Grothendieck group retains all its original actual finite-length
short-exact-sequence relations, including nonsplit sequences.

The index, group and representation-carrier universes `uI`, `uG`, `uV`
are independent. The composite and class formula use the original
`max uG uV` carrier saturation. The statement is for all `I`, `J` and `n`,
so it specializes to every minimum representative and every normalizer
section in the rational target. It imposes no field, rank, characteristic,
splitness or general-linear restriction.

The direct proof dependencies are
`geometricTargetInductionFunctor_eq_ambient`,
`geometricTermSourceAmbientIso`, `geometricTerm_hasFiniteLength`,
`SmoothRep.hasFiniteLength_of_iso`,
`geometricTermK0_ofRepresentation`,
`FiniteLengthGrothendieckGroup.ofObject_eq_of_iso`, and the elementary
composition and equality isomorphisms of functors. The source comparison
transitively uses `leviNormalizedJacquetAmbientIso`,
`leviInverseHalfCharacter_eq`, generic pullback/twist isomorphisms, and
right whiskering. The target equality transitively uses
`leviNormalizedInductionFunctor_eq_ambient` and
`closedHalfCharacter_subgroupOf`. Both compare the same radical's Haar
normalization using the continuous subgroup identification and the
published `Geometric.haarChar_eq_of_conjugacy`; their normalizer inference
uses `normalizes_of_subgroupOf`.

The actual term's finite-length and K0 generator proofs also use
finite-length preservation under continuous group equivalence pullback.
That chain reduces through
`FiniteLengthAssembly.finiteLength_comp_surjective_iff` to the generic
subrepresentation order isomorphism
`CuspidalSupport.JacquetLength.compSubrepresentationOrderIso`.
The import closure contains broader representation infrastructure,
including `GeneralLinearDerivativeDeterminantTwistProof` through the source
adapter; only its generic pullback/twist isomorphisms occur in this proof
chain. No proof in this chain uses a geometric lemma, adjointness,
cuspidal-support existence or uniqueness, character independence, or
Langlands classification theorem.

Each endpoint comparison concerns two presentations of its own radical.
This construction neither relates the distinct source and target radicals
nor establishes either orbit Haar correction. The actual rational orbit
enumeration and open ordering, geometric filtration and normalized
graded-piece identifications, distinct-radical modulus balance, any
compact/full induction comparison, and the whole
`RationalGeometricK0ExpansionStatement` remain separate obligations.

Author: Worker 184.
