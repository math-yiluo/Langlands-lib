# Actual lattice base change for split tori

Worker 146. The imported cocharacter-lattice base-change construction and its
finite-Galois descent development are by Worker 1272.

For commutative integral domains `k` and `K`, a scheme map
`b : Spec K ⟶ Spec k`, and a commutative group scheme `T` over `Spec k` whose
underlying group is a split torus, this module constructs canonical additive
equivalences

- `cocharacterLattice.baseChangeEquiv b T hT`, from the actual cocharacters of
  `T` to the actual cocharacters of its pullback;
- `characterLattice.baseChangeEquiv b T hT`, from the actual characters of
  `T` to the actual characters of its pullback.

The forward maps are exactly `cocharacterLattice.baseChange` and
`characterLattice.baseChange`. The maps do not depend on a choice of splitting:
a splitting is used only to prove their bijectivity. These are equivalences of
integral additive groups, with no tensoring or denominators. Their scope
includes all field extensions, with no finiteness, separability, characteristic
or positive-rank hypothesis.

## Provenance and construction

This is an internal derived development of the published actual Hom lattices,
integer classification of endomorphisms of the multiplicative group, coordinate
lattice equivalences, and natural point models in `Torus.Lattice` and
`Torus.Split`. It also uses the actual cocharacter pullback construction in
`Absolute.CocharacterDescentLattice`, rather than introducing a second lattice
base-change map. No additional assertion from original literature is used.

`cocharacterLattice.groupHom_baseChange_dynamic` checks definitionally that the
underlying homomorphism of the additive pullback is precisely
`Dynamic.baseChangeCocharacter`. The lemmas `baseChange_comp` and
`baseChange_precomp` establish naturality for cocharacters and characters,
respectively. `CommGroupScheme.isoOfGroupIso` changes an isomorphism of the
underlying group schemes into the additive notation of commutative group
schemes.

`gmEndEquiv_baseChange` expresses an endomorphism as its integer multiple of the
identity. Additivity of pullback and cancellation of the canonical
multiplicative-group comparison preserve that integer. Applying this result to
the composite of a cocharacter and a character proves
`latticePairing_baseChange`, for any commutative group scheme over these domain
spectra, without a splitness hypothesis.

For the coordinate split torus, `splitTorus.commBaseChangeIso` is the existing
canonical split-torus comparison in additive notation.
`pointsEquiv_baseChangeIso_hom` and `commBaseChangeIso_hom_proj` verify, on every
test scheme, that this comparison preserves the unit coordinates and coordinate
projections. Consequently `cocharacterLatticeEquiv_baseChange` preserves each
integer coordinate: composing with a projection reduces the claim to the
endomorphism calculation. The coordinate lattice equivalences then prove
injectivity and surjectivity of actual cocharacter pullback.

The coordinate cocharacters also pull back to the same coordinate
cocharacters, as checked by their dual coordinate projections. Composing each
of them with a character proves `characterLatticeEquiv_baseChange` by the same
integer endomorphism argument, and hence bijectivity for characters.

For an arbitrary split torus, choose an isomorphism to a coordinate split
torus. Naturality gives the commuting squares between the two pullback maps.
The isomorphism and its inverse transfer injectivity and surjectivity to the
original torus. `AddEquiv.ofBijective` packages each canonical forward map
using the proved bijectivity.

## Actual cocharacter descent and scope

`IsSplitTorus.existsUnique_baseChangeCocharacter` states that every actual
homomorphism `Gm_K ⟶ T_K` is the dynamic base change of a unique integral
cocharacter of the original `T`. It follows from the cocharacter bijection and
the definitional Dynamic comparison. In particular, a cocharacter of a fixed
split torus obtained over an algebraic closure descends to that same torus.

This is a descent prerequisite for fixed-torus parabolic classification. It
does not prove that a geometric parabolic is a dynamic subgroup, construct root
data, or establish any parabolic equality.
