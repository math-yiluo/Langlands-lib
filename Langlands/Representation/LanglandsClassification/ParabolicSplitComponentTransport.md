# Transport from standard-Levi annihilators to a split component

Module
`Langlands.Representation.LanglandsClassification.ParabolicSplitComponentTransport`,
namespace `Langlands.GroupScheme`.

These are internal derived lemmas for the published
`ParabolicSplitComponentChamberStatement`. They use the definitions and proved
compatibility results in [ParabolicChamberStatements](ParabolicChamberStatements.md)
and the restriction results in
[LanglandsCharacterRestriction](../../GroupScheme/Rational/LanglandsCharacterRestriction.md).
They introduce no new source-dependent mathematical assertion: every complement,
range, existence, and uniqueness hypothesis needed by a lemma is explicit.

## Setting

Fix a field, an affine group scheme `G`, a commutative group scheme `T` embedded
monomorphically in `G`, a cocharacter `ν`, reflection data `D`, a set `J` of
characters, and a morphism `f : A → T`. Write `r` for real character restriction
along `f` and `F` for its real cocharacter map. The principal hypotheses are that
`F` is injective, its range is `rootAnnihilator T J`, both tori are split when
restriction duality is used, and `corootAnnihilator i D J` complements the real
span of `J`.

## Restriction and projected roots

`splitComponent_restrict_bijOn` combines the published surjectivity of `r` with
the equality of its kernel and the real span of `J`. The published unique
preimage lemma for a complement gives bijectivity of `r` on the coroot
annihilator. For a projected root, the difference from its original root is in
that kernel. This proves `restrict_eq_of_mem_projectedRoots` and, when every
selected projection exists, `restrict_image_parabolicRoots`.

For `splitComponent_root_injective`, choose projected representatives for two
simple roots outside `J`. Equality after restriction implies equality of these
representatives by injectivity on the annihilator. The explicit separation
hypothesis for projected roots then identifies their original labels.

## Chambers and unique lifts

`splitComponent_pairCondition_iff` works for any predicate on real numbers.
Choose the unique annihilator lift of a character of `A`, lift each projected
coroot through the specified range of `F`, and use adjunction of `r` and `F`.
Pairing in the annihilator is unchanged by projecting the coroot. The converse
uses the original-root label in the restricted-coroot relation. Strict
positivity and nonnegativity give `splitComponent_openChamber_eq` and
`splitComponent_closedChamber_eq`.

`splitComponent_coroot_existsUnique` pulls a unique projected coroot back
through `F`. Separation of restricted roots fixes its label, and injectivity of
`F` gives uniqueness. For `splitComponent_fundamentalCoweight_existsUnique`,
the published `parabolicFundamentalCoweights_subset` places each selected
fundamental coweight in the range of `F`; ambient uniqueness and injectivity
again give a unique preimage.

## Weight descriptions and root cones

The imported `restrictedCorootChamber_eq_image_openFace` from `SimpleCorootFaces`
and `restrictedClosedCorootChamber_eq_image` express the lifted chambers as
restriction images of the ambient simple-coroot faces.
`splitComponent_image_weight_description` transports any supplied description
of such a face by coefficients satisfying a predicate. Its reverse implication
uses ambient uniqueness of fundamental weights to replace arbitrary supplied
weight representatives by the chosen family. The central summand remains an
element of the range of restricted group characters.

For `splitComponent_image_rootPositiveCone`, restrict the defining finite sum
of the projected-root cone. The error term lies in `ker r`, so it disappears.
Conversely lift a restricted combination to the annihilator by bijectivity;
the difference from the original-root combination lies in the same kernel.
`splitComponent_image_rootNonnegCone` uses the same argument after expressing
the finite nonnegative hull by the published `RootCombination` family lemma.
That lemma permits repeated vectors, so no unstated independence hypothesis is
needed in either cone argument.
