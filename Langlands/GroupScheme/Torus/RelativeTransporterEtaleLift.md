# Pointed etale lifts of actual diagonalizable transporter points

Author: Worker 1683. The actual smooth transporter scheme and its unchanged
finite-presentation helper were authored by Worker 1621 and are reused from
the frozen `RelativeTransporterSmooth` prerequisite; both contributors are
listed in the submission.

This module is `Langlands.GroupScheme.Torus.RelativeTransporterEtaleLift`.
Its provenance is internal: it combines the proved actual smooth transporter
construction with the proved pointed smooth-section constructor and the
actual group pullback point equivalence. It uses no additional literature
assertion and assumes no local transporter section as input.

## Inputs and constructed pointed data

Let `R : CommRingCat.{u}`, let `M : Type u` be any additive commutative
group, and let `G/Spec R` be an actual group scheme with affine total
scheme and smooth structure morphism. Let
`i₁, i₂ : D_R(M) → G` be actual group-scheme homomorphisms. No
closed-immersion condition on these homomorphisms, finiteness condition
on `M`, connectedness of `G`, or Noetherian condition on `R` is imposed.

For a point `s` of `Spec R`, the supplied transporter point is
`g₀ : Over.mk ((Spec R).fromSpecResidueField s) → G.X`. Thus it is
an actual morphism `Spec κ(s) → G` over the canonical residue-field
map to the base. The input hypothesis `IsTransporter i₁ i₂ g₀` is the
existing all-refinement equation: on any scheme refining this test,
`i₁(h) g₀ = g₀ i₂(h)` for every point `h` of the diagonalizable group.

`pointedEtaleTransporter` constructs `PointedEtaleTransporterData i₁ i₂ s g₀`.
The data consist of a neighbourhood scheme `U`, an etale projection
`p : U → Spec R`, a morphism `b : Spec κ(s) → U` with `b ≫ p`
exactly the canonical residue map, and a morphism
`g : Over.mk p → G.X`. This morphism satisfies `IsTransporter i₁ i₂ g`.
Its restriction along the actual over-morphism defined by `b` is exactly
`g₀`, as an over-morphism. In particular, the supplied point and its
scalar structure are recovered exactly. Global surjectivity of `p` is
not asserted.

## Implemented construction

The proof makes the actual residue field into an `R`-algebra using
`Spec.preimage` of the canonical residue map. Its algebra spectrum is
identified with that canonical field test by an over-morphism whose
underlying scheme map is the identity. Transporter fixedness is preserved
under precomposition, so the supplied point on that affine algebra test
factors through `relativeTransporterScheme i₁ i₂` by
`exists_relativeTransporter_factor_iff`. The factorization recovers the
original scheme morphism exactly.

The existing `smooth_relativeTransporterScheme` proves that this actual
transporter scheme is smooth, including when some other fibres are empty.
Apply `Langlands.AlgebraicGeometry.pointedEtaleSection` to its structure
map and the specified residue-field point just obtained. This supplies
`U`, `p`, `b`, and a map from `U` into the transporter scheme, with exact
recovery of that point. Composing with `relativeTransporterHom` yields
`g`. The inclusion satisfies the universal transporter relation, so
restriction along the section gives the transporter relation for `g`.
The pointed section's exact recovery equation, followed by the original
factorization equation, proves the data's `recovers` equation.

## Actual pullback equation and specialization

The imported helper `IsTransporter.restrict` from
`TransporterFunctoriality` proves preservation under restriction of a test
scheme. The generic helper
`IsTransporter.baseChange_of_equiv` takes a point of the actual pulled-back
group and transfers the original transporter relation, through
`baseChangePointsEquiv`, to the two actual pulled-back homomorphisms.
It applies the injectivity of this multiplicative point equivalence,
then uses its compatibility with group maps and with refinement of
test schemes. The resulting equality is precisely the original
all-refinement transporter equation on the mapped test.

For constructed data `d`, `identityComparison` is the identity scheme
map from the terminal test over `U`, mapped to the original base, to
the test with structure map `p`. `baseChangedSection` is the inverse
image of `identityComparison ≫ g` under `baseChangePointsEquiv`.
It is therefore an actual section of `G_U` over `U`.
`baseChangePointsEquiv_baseChangedSection` proves this exact adjunction
equation. `baseChangedSection_isTransporter` proves the universal
transporter equation for the actual maps `(baseChange p).map i₁`
and `(baseChange p).map i₂`. It quantifies over every refinement of
every test scheme, rather than just rational or affine points.

Finally `baseChangedSection_recovers` proves that the composite
`Spec κ(s) → U → G_U → G`, using `b`, the constructed section and
the actual pullback projection, is exactly `g₀.left`. The proof takes
the underlying scheme map of the adjunction equation, precomposes
with `b`, and applies the data's original over-morphism recovery
identity. Together with `b ≫ p = canonical`, this is the exact
specified residue-point recovery in the original fibre.

All constructions are uniform in the arbitrary universe `u`. The
inspected constructor uses only `propext`, `Classical.choice`, and
`Quot.sound`. This unit does not prove local self-centralizer or
maximality assertions, codimension-one reductivity, or openness of
the reductive geometric identity-component locus.
