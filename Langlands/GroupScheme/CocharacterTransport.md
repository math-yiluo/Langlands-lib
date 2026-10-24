# Transport of actual group-scheme cocharacters

This is an internal construction from actual scheme pullbacks, their
composition comparison, and the established base-change isomorphism of
the multiplicative group. The generic composition comparison and its
projection formula are imported from
`Langlands.AbelianScheme.Tate.BaseChangeCoherence`; those declarations
apply to arbitrary group schemes and do not require commutativity.
No additional representability or descent datum is assumed.

## Base maps and descent

Let B and S be schemes, b:S→B, and a:S→S a scheme endomorphism satisfying
a≫b=b. Let G be any group scheme over B. Write G_b for its actual
pullback to S. An inverse for a is not needed in this generic module.

The definition `descentBaseChangeIso b a ha G` constructs the canonical
isomorphism a*G_b ≅ G_b. It is the inverse of the established pullback
composition comparison, followed by the equality isomorphism associated
to a≫b=b. This uses the fact that G_b comes by pullback from B.
The theorem `descentBaseChangeIso_hom_fst` proves that its projection to
G is the composite of the two original pullback projections. The proof
first checks compatibility of equality isomorphisms with pullback
projections, then applies `baseChangeCompIso_inv_fst`.

For a test scheme T over S, write T_a for the same scheme with structural
map T.hom≫a. The isomorphism `descentTestIso b a ha T` identifies the
B-schemes obtained from T and T_a; its underlying scheme map is the
identity. The theorem `baseChangePointsEquiv_descent` proves that the
descent isomorphism preserves points of G over B under this comparison.
The proof uses extensionality of morphisms over B and the projection
formula just proved.

## Transport and evaluation

For an actual group-scheme morphism χ:Gm_S→G_b, the definition
`transportCocharacter b a ha G χ` is the composite

\[
\mathbb G_{m,S}\xrightarrow{\sim}a^*\mathbb G_{m,S}
 \xrightarrow{a^*\chi}a^*G_b\xrightarrow{\sim}G_b.
\]

The first arrow is the inverse of `Gm.baseChangeIso a`, which preserves
units on every test scheme. Thus transport produces an actual scheme
cocharacter by composition of actual morphisms of group schemes.

The theorem `transportCocharacter_points` gives its evaluation on every
T over S. For x∈Gm_S(T), take its unit u∈Γ(T,O_T)×. Regard u as a unit on
T_a, whose underlying scheme is unchanged, evaluate χ there, and use the
identity comparison of the underlying B-schemes. Under the canonical
pullback point equivalence this is exactly the value of the transported
cocharacter at x. The Lean formula retains the `descentTestIso` arrow,
so it does not identify distinct over-category objects by assumption.
Its proof combines `baseChangePointsEquiv_descent`, naturality of
base-change points in the group morphism, and the unit-preserving formula
for the inverse multiplicative-group comparison.

The theorem `transportCocharacter_id` proves transport by the identity
is the original χ. The theorem `transportCocharacter_comp` proves

\[
T_a(T_c(\chi))=T_{a\mathbin{\gg}c}(\chi)
\]

for a and c both over B. Both proofs use equality on all test-scheme
points. The identity case compares T and T_id by their identity scheme
map. The composition case compares T_(a≫c) with (T_a)_c. Naturality of
multiplicative-group points identifies their source points with the same
unit, and naturality of pullback points identifies the target values.
These arguments establish scheme-morphism equalities, not only equality
on field-valued points.

## Points over the base

The definition `baseChangeBasePointsEquiv b G` identifies actual
S-valued points of G_b over S with actual S-valued points of G over B.
It composes the pullback point equivalence with the identity-scheme
comparison between structural maps b and id_S≫b. The theorem
`baseChangeBasePointsEquiv_left` identifies its underlying scheme map
with projection from the pullback.

The generic construction is algebraic. It does not impose continuity on
a field automorphism, identify any matrix coordinates, or prove a
cocharacter-conjugacy stabilizer description.
