# Jacquet quotients under a character twist trivial on the radical

This pair constructs the identification of actual Jacquet quotients before and
after twisting by an ambient character that is trivial on the radical. Throughout,
`R` is a commutative ring, `G` a group, `ρ : Representation R G V` an `R`-linear
representation on an arbitrary module, `N M : Subgroup G` with
`hMN : M ≤ Subgroup.normalizer N`, and `χ : G →* Rˣ` a character with
`hN : N ≤ χ.ker`. The ring, the group and the two representation carriers `V`
and `W` have independent universes. Only normalization of `N` by `M` is used;
`N` need not be normal in `G`. No topology, smoothness, finiteness or
admissibility assumption appears.

## Restricted actions and relation submodules

`twist χ ρ` acts by `g ↦ χ(g) • ρ(g)`. For `n ∈ N` the scalar `χ(n)` is `1`,
so `twist_apply_of_le_ker` gives `twist χ ρ n v = ρ n v`, and
`twist_comp_subtype` gives equality of the restricted
representations `(twist χ ρ).comp N.subtype = ρ.comp N.subtype`. Consequently
`relations_twist_of_le_ker` proves that the relation submodules spanned by the
vectors `ρ(n)v - v` agree: `relations (twist χ ρ) N = relations ρ N`.

The existing theorem `Langlands.Jacquet.twist_comp_subtype`, authored by
Worker 23 in `Langlands.Representation.Classification.SupercuspidalTwist`,
has moved here with its name, statement and proof unchanged. That module
now imports this one. The duplicate restricted-action theorem was removed,
and this algebraic core still imports only
`Langlands.Representation.Jacquet.Coinvariants` and
`Langlands.Representation.Twist.Definitions`.

## The linear equivalence of actual quotients

The two quotient maps are descended through the universal property `lift` of
the actual quotients:

- `twistCoinvariantsToCoinvariants χ ρ N hN` descends
  `mk ρ N : V → Coinvariants ρ N` to `Coinvariants (twist χ ρ) N`. Its
  invariance under the twisted `N`-action is the formula
  `twist χ ρ n v = ρ n v` followed by the Library law `mk_apply_subgroup`.
- `coinvariantsToTwistCoinvariants χ ρ N hN` descends `mk (twist χ ρ) N` to
  `Coinvariants ρ N` in the same way.

`twistCoinvariantsLinearEquiv χ ρ N hN` is the linear equivalence with these
two maps as forward map and explicit inverse. Each composite is the identity
because the two linear maps agree after precomposition with the actual
quotient map (`Representation.Coinvariants.hom_ext`); on a representative both
sides send `v` to the class of `v`. The representative formulas
`twistCoinvariantsLinearEquiv_mk` and `twistCoinvariantsLinearEquiv_symm_mk`
hold by definition:

- forward: the class of `v` in `Coinvariants (twist χ ρ) N` goes to the class
  of the same `v` in `Coinvariants ρ N`;
- inverse: the class of `v` in `Coinvariants ρ N` goes to the class of the
  same `v` in `Coinvariants (twist χ ρ) N`.

## The representation equivalences

`actionTwistEquiv ρ N M hMN χ hN` is a `Representation.Equiv`

```lean
(action (twist χ ρ) N M hMN).Equiv
  (twist (χ.comp M.subtype) (action ρ N M hMN))
```

whose underlying linear equivalence is `twistCoinvariantsLinearEquiv`. Here
`action` is the Library's unnormalized descended `M`-action on the actual
quotient. The intertwining equation is checked on representatives: for
`m ∈ M`, the source action sends the class of `v` to the class of
`χ(m) • ρ(m)v`, and the target sends the class of `v` to `χ(m)` times the
class of `ρ(m)v`. These agree because the quotient map is linear.
`actionTwistEquiv_mk` and `actionTwistEquiv_symm_mk` state the representative
formulas of the forward map and of its inverse.

`twistActionTwistEquiv ρ N M hMN χ hN ψ` is the corresponding equivalence after
a common additional character `ψ : M →* Rˣ`:

```lean
(twist ψ (action (twist χ ρ) N M hMN)).Equiv
  (twist (χ.comp M.subtype) (twist ψ (action ρ N M hMN)))
```

It has the same underlying linear equivalence. The intertwining equation is
the representative computation above with the additional scalar `ψ(m)`, using
commutativity of the two scalar actions. Its representative formulas are
`twistActionTwistEquiv_mk` and `twistActionTwistEquiv_symm_mk`. With
`R = ℂ` and `ψ` the inverse half of a positive modulus, this covers the
normalized Jacquet action; that specialization is stated in the companion
module `Langlands.Representation.Jacquet.NormalizedCharacterTwistEquiv`.

## Naturality

Let `σ : Representation R G W` and let `f : ρ.IntertwiningMap σ` be an
ambient intertwiner. `twistIntertwining χ f` is the same linear map, regarded
as an intertwiner of the twists, and `map N M hMN` is the Library's induced map
of actual quotients.

- `actionTwistEquiv_naturality` is the commuting square
  `twistIntertwining (χ.comp M.subtype) (map N M hMN f) ∘ e_ρ =
  e_σ ∘ map N M hMN (twistIntertwining χ f)`, with `e_ρ`, `e_σ` the two
  instances of `actionTwistEquiv`.
- `actionTwistEquiv_map_apply` is the same square evaluated at an arbitrary
  element of the twisted quotient.
- `actionTwistEquiv_symm_naturality` is the square for the inverse
  equivalences.
- `twistActionTwistEquiv_naturality`, `twistActionTwistEquiv_map_apply` and
  `twistActionTwistEquiv_symm_naturality` are the same three statements for
  the common-`ψ` equivalence, with `twistIntertwining ψ` applied to the
  induced maps.

All squares are proved by intertwiner extensionality and quotient
extensionality: on the class of `v` both paths give the class of `f v`.

## Provenance and scope

This is internal algebraic infrastructure, derived directly from the
definitions of the actual coinvariant quotient (`Coinvariants`, `relations`,
`mk`, `lift`, `action`, `map` in `Langlands.Representation.Jacquet.Coinvariants`)
and of the character twist (`twist`, `twistIntertwining` in
`Langlands.Representation.Twist.Definitions`). It formalizes the elementary
observation that a character trivial on `N` does not change the `N`-relations,
so twisting commutes with taking `N`-coinvariants. No literature result is
imported or asserted; the quotient constructions themselves carry the
literature citations recorded in their own Markdown.

The existing statement `Langlands.Jacquet.CoinvariantTwistStatement` in
`Langlands.Representation.Jacquet.AlgebraStatement` concerns a subgroup normal
in all of `G` and the full ambient twisted action; this pair does not change it
and works with the more general normalizer action of `M`.

The pair asserts only these algebraic identifications and their naturality. It
does not select a Weyl branch, assert any analytic continuation, assert generic
occurrence of a constituent, or compare Jordan–Hölder multiplicities.
