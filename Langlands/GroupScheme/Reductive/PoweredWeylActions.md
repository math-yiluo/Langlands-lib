# Square and fixed actions for powered Weyl families

This derived unit supplies two Weyl-action steps for maps used in
the split isogeny construction. It does not require the powered maps
to represent whole root subgroups. Its generic square and fixed-action
statements work over an arbitrary commutative ring and arbitrary
ambient group scheme.

`HasRootConjugationFormula` retains just the actual source-character
conjugation identity on every scheme test. It omits the representation
and closed-immersion requirements of a root parametrization.
`wordConj_square_of_rankOneLaws` proves that conjugating a map twice
by the Weyl product of the supplied opposite pair equals precomposing
that map by multiplication by
`((P.pairingIn ℤ a c).negOnePow : ℤ)`, cast into the original ring.
Its inputs are the standard integral coordinate-pairing identity,
the existing exact rank-one laws for the opposite pair, and the
source-character conjugation formula for the map being conjugated.
In the powered-family application those are supplied by the powered
rank-one and equivariance results.

The proof extracts the actual original-base coroot square from the
rank-one laws. Character evaluation on this coroot at minus one
gives the displayed sign. Even and odd exponents identify the result
with its raw base-ring cast. The point formula for word conjugation
and affine-test detection of homomorphism equality give the exact
map identity. No chosen sign-unit construction is used.

`PointsCommute.precompose` shows that two commuting maps remain
commuting after arbitrary separate additive-line homomorphisms are
precomposed. This includes characteristic power maps and needs no
coordinate formula or characteristic condition of its own. Every
additive-line point is the scalar point of its actual coordinate,
so the original commutation identity applies to the new coordinates.

`wordConj_fixed_of_pointsCommute` proves that the Weyl product acts
trivially on a map commuting with both supplied opposite root maps.
All three evaluated factors of the Weyl product commute with that
map, so their product does too.

`PoweredWeylActions.wordConj_fixed_of_source_noCone` supplies this
fixed action from the exact source no-cone hypotheses. Here the
coefficient ring is local, the actual target is reductive with a
closed fibrewise-maximal coordinate split torus and full root datum,
and the root-datum isogeny satisfies the host characteristic
condition. Actual corresponding target root maps are supplied at
the positive source root, its negative, and the root being conjugated.
The three maps in the requested identity are their separately
precomposed images. The included no-cone theorem proves commutation
of the genuine target maps, including the exceptional cases.
Precomposition preserves it and the three-factor argument gives
the fixed map identity. The precomposition identities are the
existing powered-family and word-transport identities in the
intended application; no powered-parametrization premise is added.

`WeylSquareAndFixedActionStatement` records the two generic map
identities and `weylSquareAndFixedAction` proves them. The provenance
is generalization of the published coroot-square point calculation
to the supplied character formula, coordinate-preserving evaluation,
group algebra, and the included actual-root no-cone theorem.
Instantiating the generic lemmas with the complete powered family
uses its rank-one, equivariance and word formulas; that wrapper and
the remaining U1 and global isogeny assembly are separate work.
