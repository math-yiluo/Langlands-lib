# Selection of irreducibles by the unramified twist class of a supercuspidal support

Over a `p`-adic field `E` with topological data `T`, fix a multiset `s` of
cuspidal data. This module defines the representations of `GL_n(E)` whose
supercuspidal support is an unramified twist of `s`. It proves that all
selected representations have nonzero fixed vectors at one compact open
level.

## The selection

- `unramifiedFieldCharacter T c` is the smooth character `a ↦ c ^ ord(a)`
  of `Eˣ`. `isSmooth_universeLift_twist_determinantUnramified` records
  that unramified twists and universe lifts preserve smoothness.
- `supportTwistSelection T n s W π` says that `π`, on a carrier in
  universe `z`, is smooth and has the following property for some
  `c : ℂˣ`: the universe lift of `twist (determinantUnramified E n c) π`
  has supercuspidal support `s`.
- `supportTwistSelection_of_equiv`: the selection is invariant under
  equivalence.
- `supportTwistSelection_of_isUnramifiedTwistOf`: if `τ` has support `s`,
  every unramified twist of `τ` equivalent to `π` makes `π` selected. The
  twisting character has the form `determinantUnramified E n c₀`
  (`eq_detOrderCharacter_of_isUnramified`), and the parameter `c₀⁻¹` undoes
  it.
- `supportTwistSelection_iff`: let `π` be equivalent to an irreducible `D`
  with support `s'`. Then `π` is selected exactly when
  `s'.map (CuspidalDatum.characterTwist (unramifiedFieldCharacter T c)) = s`
  for some `c`. Twisting `D` twists its support
  (`IsSupercuspidalSupport.characterTwist`), and supports of irreducibles
  are unique (`glSupercuspidalSupportUniqueness`).

## Finitely many products

- `sum_rank_of_ofFn_eq`, `mem_toFinset_of_ofFn_eq` and
  `cuspidalProductInduced_hasFiniteLength` are auxiliary facts. The last
  one says that supercuspidal products have finite length, by
  `irreducibleProductFiniteLength`.
- `exists_finite_cuspidalProducts_covering`: for `s` of total rank `n`,
  finitely many supercuspidal products of finite length contain every
  irreducible representation with support `s` as a subquotient. The index
  type is the finite set of orderings
  `f : Fin (card s) → s.toFinset` with `List.ofFn f = s`. Each element of
  `s.toFinset` gets a chosen supercuspidal representative of its class.
  `isCuspidalConstituent_iff` identifies support constituents with
  subquotients of the corresponding product.

## One compact level

`exists_compact_fixed_of_supportTwistSelection`: assume arbitrarily small
compact open subgroups are stable under `θ⁻¹`, for
`θ = entrywiseAut σ n`. Then there is one compact open subgroup `J` such
that every selected representation has a nonzero `J`-fixed vector. The
proof applies `exists_compact_open_fixed_constituentTwists` to the finitely
many covering products. That lemma gives fixed vectors of all invariant
unramified twists of their irreducible subquotients at one level. A
selected representation is such a twist: if
`twist (determinantUnramified E n c) π` has support `s`, then `π` is its
σ-invariant unramified twist by `determinantUnramified E n c⁻¹`.

The level `J` here is obtained by uniform visibility: it comes from the
subquotients of finitely many supercuspidal products and their
σ-invariant unramified twists, not from a statement in the literature.
The support conditions of the twisted Paley–Wiener theorem in
Henniart–Lemaire (2011), II.5.7, p. 105, are vanishing conditions on a
functional `Φ`. Condition (i) asks that `Φ` vanish outside finitely many
σ-stable elements of `B(G(E))`, the set of inertial equivalence classes
of cuspidal pairs. Condition (i)′ of Remarque (1) asks that `Φ` vanish on
the strongly irreducible σ-representations without nonzero `J`-fixed
vectors, for some compact open `J`. The remark cites Bernstein, *Le
« centre » de Bernstein* (1984), 3.7 and 3.9, for replacing (i) by (i)′.
In the Library, the counterpart of (i)′ is the `J`-invisible span inside
the complementary span. The lemma above gives one level at which every
selected representation is visible. Unramified twists of a
representation act on its supercuspidal support by twisting each
cuspidal datum by the same unramified character. So the selection here
is contained in one inertial class.
