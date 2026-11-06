# Rational compatible tori and their separating cocharacters

This internal construction works over an arbitrary field `k : Type u`. Let
`a : A → G` be an actual split closed subtorus of an affine group locally of
finite type, and let `j : M → G` represent its all-test centralizer.

`torusCentralizerRationalModel` chooses a maximal torus `T` over the original
field containing `A`. It provides its actual inclusions into `G` and `M`, a
closed inclusion `A → T`, and the two commuting composition identities. Both
inclusions of `T` are maximal over `k`. No splitness of `T` or algebraic
closedness of `k` is assumed.

The construction applies the published finite-type maximal-torus extension
theorem to `a`. Commutativity of `T` puts its image in the represented
centralizer, so the representation factors the inclusion through `M`. Closedness
of `j` and maximality in `G` imply maximality in `M`. The closedness of `A → T`
is reflected from its composite with the closed inclusion `T → G`.

For a supplied proof that `A` is split, `cocharacter` composes the published
original-field centralizing cocharacter of `A` with `A → T`. The identity
`cocharacter_centralizer` states that its actual dynamic centralizer is exactly
the original all-test torus centralizer.

The three base-change lemmas retain this particular original-field cocharacter.
For an arbitrary morphism of base schemes, its canonical base change presents
the base change of the original torus centralizer, is represented by the base
change of `j`, and equals the centralizer of the actual base-changed subtorus.
The proof uses the compatibility of actual cocharacter base change with
composition, dynamic-centralizer base change, represented-subgroup base change,
and torus-centralizer base change. It makes no new cocharacter choice over the
new base.

For any field extension `E/k`, `cocharacter_baseChange_galois` proves that this
cocharacter is fixed by the ordinary cocharacter Galois representation for
every `k`-algebra automorphism of `E`. This is the published fixedness theorem
for canonical base change, specialized to the chosen original-field
cocharacter. The field extension need not be finite or Galois.

When `M` is also affine and locally of finite type, `relativeRoots_eq_pairing`
identifies its actual roots for the same acting torus with the ambient actual
roots having zero pairing with this cocharacter. The companion
`relativeRoots_baseChange_eq_pairing` proves the same statement after any
field base map, using the canonical base change of the original cocharacter.
These statements use the published dynamic Lie theorem and the exact
represented centralizer; they require neither splitness nor maximality of the
base-changed acting torus.

This is a derived internal construction from the published maximal-torus
extension, represented centralizer factorization, actual lattice Galois
fixedness, and dynamic Lie comparisons. It supplies rational geometry for the
Levi cocenter root model. It does not establish preservation of maximality
under field extension, construct a finite splitting field or an actual root
datum, identify the derived coroot span, or construct based root descent data.
