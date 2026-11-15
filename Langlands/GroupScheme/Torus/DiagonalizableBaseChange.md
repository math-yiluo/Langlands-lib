# Base change of diagonalizable group schemes

This derived construction compares the existing diagonalizable group schemes
after an arbitrary morphism `b : Spec R' → Spec R` of affine base schemes.
The rings are arbitrary commutative rings in one universe, and `Λ` is an
arbitrary abelian group in that universe. No finite-generation, freeness,
reducedness or characteristic condition is imposed.

`Langlands.GroupScheme.Diagonalizable.baseChangeIso` is an actual group-scheme
isomorphism

`b* D_R(Λ) ≅ D_R'(Λ)`.

`commBaseChangeIso` is its lift to the existing category of commutative group
schemes. In particular, the construction retains finite diagonalizable groups
with torsion character groups and nonsmooth fibres.

For every test scheme `U` over `Spec R'`,
`baseChangeCharacterPointsEquiv` identifies points of the left side with
`Hom(Multiplicative Λ, Γ(U, O_U)ˣ)`. The comparison isomorphism preserves this
entire character-valued point. The two simp lemmas describe its forward and
inverse effects on these points. All tests are allowed, including nonaffine
and nonreduced schemes.

The implementation composes the published `baseChangePointsEquiv` with the
published `Diagonalizable.characterPointsEquiv` on the test viewed over
`Spec R`. Naturality follows from the naturality of those two equivalences.
`isoOfPoints` constructs the actual group-scheme isomorphism from that natural
multiplicative equivalence. The inverse formulas follow from the corresponding
`isoOfPoints` formulas. The commutative comparison uses the same homomorphisms.

This is an internal consequence of the Library's all-test corepresentation
and pullback constructions, following the same point-model method as the
published `Gm.baseChangeIso` in `Langlands/GroupScheme/Multiplicative.lean`.
It uses `Diagonalizable` and `KernelDiagonalizable` for the group-algebra
model and its all-test character interpretation. No new assertion from external
literature is used, and no classification or finite splitting theorem is
claimed here.
