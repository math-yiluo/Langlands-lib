# A structural reduction for generic minimal rational parabolics

Author: Worker 1298.

This is an internal, derived reduction toward the exact published
`GenericMinimalParabolicStatement`. It does not prove any of its structural
premises, and is not an unconditional proof of that statement.

`nonnegative_relativeRoot_support_reverse_of_generic` is an elementary
integer-sign argument for the published relative roots and lattice pairing.
If the nonnegative support of a cocharacter `η` is contained in that of a
generic cocharacter `ν`, and the actual relative roots are stable under
negation, the reverse support inclusion holds. For a root nonnegative for
`ν`, genericity makes its pairing strictly positive. A negative pairing
against `η` would make the opposite root nonnegative for `η`, hence
nonnegative for `ν`, a contradiction.

`generic_dynamicParabolic_eq_of_le` applies this observation to the
explicit premises `RelativeRootSignInclusionsStatement` and
`RelativeRootNegationStatement`. The order and equality are those of the
actual dynamic subgroup functors on every test scheme. The torus is an
actual maximal split torus; the field and universe are arbitrary.

`innerIso_hom_comp_groupHom` expresses naturality of inner conjugation
under a group-scheme homomorphism. Its proof evaluates on all test points,
where homomorphisms preserve products and inverses and take the constant
point family to the family of the image point.

`exists_conjugate_cocharacter_on_torus_of_parabolic_le` retains the explicit
premises `CocharacterMaximalSplitTorusStatement` and
`SmoothMaximalSplitTorusConjugacyStatement`. It also takes a closed
representative `j : P ⟶ G` of the larger dynamic parabolic, with `P` smooth
and connected. Given a cocharacter `χ` whose dynamic parabolic is contained
in the larger one, it factors `χ` through a maximal split torus `S` of `G`.
The published lifting lemma lifts both `S` and the chosen torus `T` to
maximal split tori in `P`. Conjugacy inside `P` gives a base point `p` and
an isomorphism from `S` to `T`. Naturality of inner conjugation then gives
a cocharacter of `T` conjugate to `χ` by the image `g` of `p` in `G`.
Representability proves that `g` belongs to the larger parabolic on the
base test scheme.

`parabolicConjugatingPoint` chooses such a point `g` by classical choice
from this existence result. Its specification provides a cocharacter `η`
of `T`, membership of the chosen point in the larger parabolic on the base
test scheme, and the equality expressing the conjugation of `χ` to `η`.
This is a choice of an actual point, with no uniqueness or canonicity
assertion. It retains the same structural inputs, closed representative,
smoothness, connectedness and containment assumptions.

`generic_dynamicParabolic_eq_of_le_of_structural` combines that transport
with the root-sign lemma, using the chosen point and its specification.
Conjugation by `g` preserves the larger subgroup
functor, because `g` belongs to it. The all-test isomorphism pullback laws
for dynamic parabolics transport the original containment to one between
cocharacters of `T`. The fixed-torus equality then transports back. The
result concerns every smaller dynamic parabolic; it does not assert that
every rational parabolic is dynamic, or that the larger dynamic parabolic
is geometrically parabolic. The smooth connected representative and all
four named structural statements remain premises.

The minimal-parabolic goal has its source in Borel and Tits, *Groupes
réductifs* (1965), §4.15(a) and §4.16, printed pp.90–92 (PDF pp.37–39),
registered as `borel-tits-1965-groupes-reductifs`. The elementary sign
reduction and transport above are an internal proof route toward that goal; they make no
claim that the source uses the same proof. Its structural premises retain
their independent proof obligations.
