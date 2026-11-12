# Actual tempered piece offset and opposite spectral separation

Worker 135. This internal derived unit defines the actual real-part offset of
a geometric-lemma piece and proves the existing
`LanglandsTripletOppositePieceSeparationStatement`. It introduces no new
literature transcription. The proof implements the spectral step of the
already stated regularity reduction; the geometric lemma and the regularity
criterion remain separate inputs to the final regularity theorem.

## Defined offset and generic weight comparison

`GeometricLemmaIntersectionDatum.temperedPieceRealPartOffset` is defined for
an actual intersection datum, a target Levi split component, a supplied
intersection component and morphism, an original unramified character, and a
test character of the target split component. It is the normalized real part
of that test character minus the existing `unramifiedPieceRealPart` through
the original intersection maps. Defining this vector imposes no factorization,
temperedness, exponent or admissibility premise. Under those hypotheses, the
existing tempered-piece cone theorem identifies it as a vector in the target
parabolic's nonnegative cone.

The generic lemma `isGeneralizedEigencharacter_of_isGeneralizedWeight`
requires a commutative coefficient ring, a topological source group and an
ambient topological group, with a central source homomorphism. A nonzero
compact-open generalized weight space implies a uniform generalized
eigencharacter. If every uniform character space were zero, each compact
fixed-character space and both defining suprema would be zero. This
contradicts the generalized weight's nonvanishing. This direction needs no
smoothness, admissibility or local compactness assumption.

## Unconditional separation theorem

`langlandsTripletOppositePieceSeparation` has exactly the existing
`LanglandsTripletOppositePieceSeparationStatement.{u,v}` as its type. It keeps
the independent field and representation-carrier universes and every original
Langlands-triplet, opposite-parabolic and representative-data quantifier.
It proves disjointness between the inducing twist's group exponents and the
split-component generalized weights of every actual full geometric-lemma
piece strictly below the identity double coset. It adds no hypothesis.

The triplet's compatibility witness gives the original source presentation.
The proved general presentation-existence theorem supplies a presentation of
the target parabolic on the same original split component. The original
point-image intersection equality becomes the rational carrier equality
required by the opposite-cone comparison; the two original Levi embeddings
supply its same-Levi hypothesis.

For each supplied intersection datum, its existing split-component
factorization constructs the component and map used in the exponent-transfer
theorem. The triplet's tempered source is admissible, as is its original
unramified twist. The proved arbitrary-parabolic Jacquet admissibility theorem
applied inside the source Levi makes the actual normalized Jacquet module
admissible. Pullback through the actual Levi-point equivalence supplies the
transported Jacquet admissibility required by the tempered-piece theorem.
Thus neither Jacquet admissibility nor intersection component existence is
left as a premise of the separation theorem.

The strict Bruhat hypothesis includes nonidentity of the original double
coset. The previously proved original-character displacement theorem therefore
gives a nonzero vector `delta` in the source parabolic's nonnegative cone,
equal to the original Levi parameter minus the original unramified piece
parameter. A hypothetical common exponent is a generalized eigencharacter
of the full piece by the generic comparison lemma. Its defined tempered offset
`x` lies in the target cone by the published full-piece exponent bound.
The opposite-cone theorem puts `-x` in the source cone. The source cone's
proved pointedness then gives `-x + delta != 0`.

Finally, the proved irreducible tempered twist exponent theorem identifies
the hypothetical inducing exponent's real part with the original unramified
Levi parameter. Expanding the two actual differences makes
`-x + delta = 0`, a contradiction. This proves the required spectral
disjointness for every original datum. The implementation uses the bound
twist and one named intersection datum throughout to avoid repeated
elaboration of equivalent large Jacquet and induction constructions.

This unit proves the full piece-separation prerequisite. It does not by
itself prove `IsPQRegular`, the intertwining dimension statement, the
geometric lemma or the regularity criterion. All target and imported
statement pairs remain unchanged.
