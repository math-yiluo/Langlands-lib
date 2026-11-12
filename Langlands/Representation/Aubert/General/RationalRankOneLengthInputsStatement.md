# Detection and Jacquet-length inputs for rational rank-one length two

Author: Worker 62.

This module states four propositions in
`Langlands.Aubert.General.RationalPointFamily`. None of them is proved here.
They split the published target `RationalRankOneLengthTwoStatement.{u, v}`
(module `RationalCorollaryTargets`) into its two representation-theoretic
inputs. They also connect the first input to an existing published
proposition. The target pair and every pair it imports are unchanged.

## Common scope

The two input statements have exactly the binders of
`RationalRankOneLengthTwoStatement`, in the same order:

- every nonarchimedean local field `k : Type u`, including positive
  characteristic;
- every connected reductive group scheme `G` over `Spec k`, actual maximal
  split torus `i` and generic cocharacter `ν`;
- the canonical evaluation topology `pointTopology` on `RationalPoint k G.X`,
  with explicit local compactness, nonarchimedean-group and Hausdorffness
  instances;
- the premises `StandardCocharacterStatement.{u}`,
  `StandardLeviIntersectionStatement.{u}` and `HasRelativeRootSystem i`;
- closedness `hU` of every actual standard unipotent point subgroup and
  closedness `hM` of every actual standard Levi point subgroup.

As in the target, the root-system premise gives the finite enumeration
`simpleRelativeRootFintype` of the literal labels `SimpleRoot i ν`, and
`DecidableEq` is classical. The parabolic, Levi and unipotent families are
the actual `parabolic i ν`, `levi i ν` and `unipotent i ν`. The ambient
decomposition of index `I` is
`isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν I`.
The inside-Levi decompositions at `J` are
`isSemidirectDecomposition_in_levi i ν hInter hG hi hν J`. Write `i_J` for the
actual normalized induction functor `normalizedInductionFunctor` of index `J`
and `r_I` for the actual normalized Jacquet functor `jacquetFunctor` of index
`I`. Representation carriers have universe `max (u + 1) v`; `u` and `v` are
independent.

Neither input statement has a premise on parabolic closedness, projection
continuity, compact-limit radicals, finite-length preservation, Weyl or
Coxeter structure, or point normalizer and centralizer comparisons. None of
these is among the target's premises either.

In both input statements `J` is a maximal standard subset
(`IsMaximalStandard J`, that is, `J = univ.erase α`). `σ` is an actual
irreducible smooth complex representation of `levi i ν J` that is
inside-Levi cuspidal in the target's sense: for the literal inside-Levi
decompositions, every proper normalized Jacquet module of `σ` is a zero
object (`IsCorollaryLeviCuspidal`). Unlike the target, `σ` is an arbitrary
`SmoothRep` rather than a `FiniteLengthObject`, and the induction need not be
reducible. When the simple-root type is empty, no `J` is maximal and both
statements are vacuous.

The detection family is indexed by the labels `β : SimpleRoot i ν`. It
consists of the Jacquet functors `r_(univ.erase β)` along all maximal proper
standard parabolics. This family is finite and needs no Weyl identification
of its members.

## The four propositions

`RationalMaximalCuspidalJacquetDetectionStatement`. Let `D` be an actual
irreducible smooth representation of `RationalPoint k G.X`, in the same
carrier universe, that is an actual subquotient (`SmoothRep.IsSubquotient`)
of `i_J σ`. Then `r_(univ.erase β) D` is nontrivial for some label `β`.

`RationalMaximalCuspidalJacquetBudgetStatement`. The actual composition
lengths `repLength` of the representations `r_(univ.erase β) (i_J σ)` sum to
at most two over all labels `β`. The sum is taken in `ℕ∞`, so the bound also
excludes infinite length of each term.

`RationalRankOneLengthTwoFromInputsStatement.{u, v}`. The detection statement
and the budget statement, at the same universes, together imply
`RationalRankOneLengthTwoStatement.{u, v}`.

`RationalMaximalCuspidalJacquetDetectionFromExtractionStatement.{u, v}`. The
published proposition `RationalCuspidalJacquetFactorExtractionStatement.{u, v}`
implies the detection statement at the same universes. That proposition has
no published proof; its proof task is
`e6add7c5-44c5-45ea-afe9-7f48c98fb927`. Let `π` be a subquotient of the
induction of an irreducible cuspidal representation, and let `τ` be an actual
irreducible cuspidal factor of a standard Jacquet module of `π`. The
proposition then supplies one rational point `n` with an actual root
association and an actual isomorphism of `τ` with the conjugate of the
inducing representation by `n`. Its point normalizer and centralizer premises
`hN` and `hZ` are not premises of the implication. The intended proof
discharges them with the published proof `rationalWeylComparison`.

## Intended use and provenance

The provenance is derived. The four propositions are an internal
decomposition of the proof route for the published target. They are not
quotations of a source.

The two inputs are the hypotheses of the published finite exact-family
criterion `Langlands.exactFamilyLengthBound`, specialized to the coatom
Jacquet family. Exactness of each `r_(univ.erase β)` is not an input. It
follows from the published `jacquetFunctor_map_isShortExact`, because the
published
`standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement`
gives compact-limit radicals from the target's own premises. With the
published nonzeroness proof `rationalStandardInductionNonzero` and the
published extraction `exists_hasTwoConstituents_of_length_le_two`, a length
bound of two gives the target's two actual finite-length irreducible factors.
This is the content of the implication
`RationalRankOneLengthTwoFromInputsStatement`.

The mathematical content of the inputs is the length argument for induction
from a cuspidal representation of a maximal Levi. The Library's reviewed
records give the source context. The pair `RationalCorollaryTargets` cites
Aubert 1995, proof of Corollary 1.10(b), printed p.2183, and Casselman 1995,
section 7.1, Corollary 7.1.2 and Theorem 7.1.4, printed pp.67–68. The pair
`RepresentedJacquetLengthWitnessStatement` records Renard 2026, VI.5.4,
printed pp.173–174, where the proof sums Jacquet lengths over the standard
Levis conjugate to the inducing Levi. That pair also records that VI.5.3 bounds
the image lengths, that VI.2.1 with VI.5.3 gives detection, and that V.4.8,
printed p.122, gives total budget two for a maximal proper Levi. I did not
reread these originals for this unit. The locators above are those recorded
in the cited reviewed Markdown.

In that route, detection comes from three facts. Every irreducible `D` has
an irreducible cuspidal subquotient of some standard Jacquet module. By the
geometric lemma, such a factor of a subquotient of `i_J σ` is a conjugate of
`σ` on an associated standard Levi. An associate of a maximal standard
subset is again maximal. The budget comes from the geometric filtration of
`r_I (i_J σ)` for each coatom `I`. Cuspidality of `σ` leaves only the pieces
whose representatives conjugate `L_J` onto `L_I`, and each such piece is
irreducible. Counting these pieces over all coatoms gives at most two.

The represented-parabolic analogue of the combined inputs is the published
`RepresentedParabolic.MaximalLeviSupercuspidalJacquetLengthWitnessStatement`.
It concerns arbitrary represented maximal parabolics, not the actual standard
families of this target, and it is not used here.

## What remains open

This module proves nothing. The two implications are to be proved in
separate proof units. The two input statements remain open. The budget
statement needs the geometric lemma for the actual standard families and the
coatom count. The extraction statement used by the last implication needs
the same geometric lemma. These are representation-theoretic obligations.
They do not belong to the parent's external Chapter V structural boundary,
and this module does not move them there.
