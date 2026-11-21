# Factorization of a restricted conjugate subgroup family

`Langlands.GroupScheme.TorusSubgroupModuli.restrictedFamilyFactorization` works
over an arbitrary scheme `S`. Suppose group-scheme homomorphisms `q : G ⟶ Q`,
`d : D ⟶ Q`, `m : Q ⟶ L` are given, with `d ≫ m` a closed subgroup inclusion.
Let `j : K ⟶ L_M` be a closed subgroup family over `M`, and let `f : G.X ⟶ M`
be a parameter map over `S` whose evaluated family is, on all tests, the
conjugate family of `d ≫ m` by the group-valued parameter `q ≫ m`.

For `b : T ⟶ M` and `s : W ⟶ T.left`, suppose the restriction of `b` along `s`
is `g ≫ f` for a point `g` of `G` on `W` over `S`. Write `B = K_T` for the
source of the evaluated inclusion `familyHom j b : B ⟶ L_T`. The construction
returns an actual isomorphism `B_W ≅ (D_T)_W` and an actual homomorphism
`B_W ⟶ (Q_T)_W` whose composite with `(m_T)_W` is the base change of
`familyHom j b`. Here the `W`-subscript uses the supplied map `s`, including
for the groups already pulled back to `T.left`.

Successive evaluation, invariance under equality of subgroup ranges, and the
restriction formula for a conjugate family identify the all-test ranges after
direct pullback to `W`. Both inclusions are closed, hence monomorphic. The
uniqueness isomorphism for represented subgroup functors therefore compares
their sources over the direct pullback of `L`. The projection of `g` through
`q` gives a point of the direct pullback of `Q`. Conjugating the direct
pullback of `d` by this point gives the lifted inclusion because inner
automorphisms commute with group homomorphisms. The canonical comparisons of
iterated with direct pullbacks transport both the source isomorphism and the
factorization to the specified groups.

This is an internal consequence of the Library evaluation and pullback
identities. In the Task 7782 valuation argument `W` is the fraction-field
spectrum and `Q` is the graph quotient; the construction supplies both the
generic lift and the source isomorphism needed there. It does not extend the
lift to `T`, require `m` to be a monomorphism, or assert that `f` is a quotient.
