# Self-normalization from a dynamic retraction

This internal proof helper is derived from the all-test retraction argument in
`Rational/DynamicLeviConjugacyReduction`, adapted to normalizer functors.
It works over an arbitrary base. The dynamic triviality and self-normalization
results assume that the ambient structural morphism `G → S` is separated
(`IsSeparated G.X.hom`). Their remaining hypotheses specify a dynamic parabolic,
a section and retraction with exact dynamic unipotent kernel, and a global
unipotent point conjugating the original cocharacter into the section.

`normalizerPointsEquivOfRetraction` constructs the canonical multiplicative
equivalence from normalizer points to section points once self-normalization is
known. Its forward map is composition with the retraction, and its inverse is
composition with the section. This construction only needs a retraction and
self-normalization; it requires neither dynamic hypotheses nor separatedness.

A normalizing point in the kernel centralizes the section: conjugation preserves
the section, and applying the retraction identifies each conjugated point with
the original point. This centralization lemma also requires no separatedness.
It implies that the point centralizes the projected cocharacter. After
conjugation by the supplied unipotent point, it belongs to both the original
dynamic centralizer and the dynamic unipotent subgroup. Separatedness gives
uniqueness of the dynamic limit, so this intersection contains only the identity.
For an arbitrary normalizing point, remove its section component to obtain such
a kernel point. These arguments test every refinement, including nonreduced
schemes.

The helper asserts no relative parabolic or relative radical transport theorem.
It is an algebraic step toward the self-normalization assertion of Conrad,
*Reductive group schemes* (2014), Corollary 5.4.6.
