# Exact Henselian lifting of split-torus transporters and normalizers

This derived module supplies the integral normalizer lifting step needed in the
proof of Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (2023), Theorem
8.2.9, printed pages 293–295, especially page 294 (PDF pages 324–326). Its
provenance is an assembly of published smooth diagonalizable-transporter
representability, exact Henselian sections, and integral-coordinate extension
of field split-torus automorphisms. The registered source is
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
The normalizer lifting statement here has broader hypotheses than the
rank-one application in that source.

All rings, fields and schemes use the common arbitrary universe `u`.
For the lifting statements, `R` is a commutative Henselian local ring, `k`
is a field with an `R`-algebra structure, and the algebra map `R → k` is
surjective. Thus `k` is a supplied residue-field presentation. The actual
ambient group scheme `G` over `Spec R` is smooth and affine. A split torus
map need not be a closed immersion or a maximal torus. No domain, DVR,
Noetherian, connectedness, reductivity, or algebraically closed residue-field
hypothesis is imposed by these lifting statements.

## Exact transporter lifting

In the namespace `PointwiseSchemeAction`,
`exists_henselian_transporter` takes two actual homomorphisms from the
same diagonalizable group `D_R(L)` into `G`, where `L` is any additive
commutative group in universe `u`. Its input point `g₀` is an over-morphism
from `Spec k` to `G`, with its prescribed structural map `Spec k → Spec R`.
The hypothesis `IsTransporter` is the published equation on every scheme
refinement and every source point. The theorem constructs an actual section
`g : Spec R → G` with that transporter property and whose restriction to
`Spec k` is exactly `g₀`.

The proof factors `g₀` through the actual relative transporter scheme using
`exists_relativeTransporter_factor_iff`. The published
`smooth_relativeTransporterScheme` proves this scheme smooth over `Spec R`.
`HenselianSections.exists_section_of_smooth_of_surjective` then gives a
section through the specified residue point. Composing with the universal
transporter morphism gives `g`; restriction of its universal equation proves
the transporter property, and the section recovery equation proves exact
residue recovery.

`exists_henselian_transporter_of_sourceIso` gives the same conclusion for a
source equipped with an actual isomorphism from a diagonalizable group. It
precomposes the two maps with the isomorphism and reflects their transporter
equation using its inverse. `exists_henselian_transporter_of_split` applies
this to any actual split torus, using a chosen splitting and the published
`Diagonalizable.splitIso`. Neither theorem changes the prescribed residue
point.

## Extending a field-fibre automorphism

`IsSplitTorus.automorphism_fieldBaseChange_surjective` is independent of the
Henselian setup. Its base `S` is any scheme, `b : Spec k → S` is any field
point, and `T` is an actual split commutative torus over `S`. Every actual
automorphism of its pullback to `Spec k` is the pullback of some actual
automorphism of `T`. The equality concerns group-scheme isomorphisms and all
their maps, rather than only their actions on rational points. The theorem
asserts surjectivity, with no assertion of uniqueness over arbitrary `S`.

The proof chooses a splitting of `T`, compares its pullback with the standard
coordinate torus, and conjugates the supplied automorphism into coordinates.
The published `splitTorus.fieldAutomorphismExtension` extends those integral
coordinates over `S`. Conjugating back supplies the required automorphism;
its published base-change equation and cancellation of the splitting maps
prove exact recovery.

## Exact normalizer lifting

`isNormalizingPoint_of_isTransporter` works over any base, without torus or
smoothness assumptions. For `i : T.toGrp → G`, `σ : T ≅ T`, and an actual
section `n`, the all-test transporter equation between `σ.hom ≫ i` and `i`
implies the published predicate `IsNormalizingPoint i n σ`. This predicate
means the equality of actual homomorphisms
`i ≫ int(n) = σ.hom ≫ i`, with commutative homomorphisms read in the
underlying group category. The proof tests the equation on every scheme and
point, multiplies by the inverse of `n`, and applies homomorphism extensionality.

`exists_henselian_normalizer_of_automorphism` takes an automorphism `σ` of
the integral split torus and a specified actual residue section `n₀` that
normalizes the pulled-back map with automorphism `σ_k`. It constructs an
actual integral section `n` with `IsNormalizingPoint i n σ` and
`baseChangeSectionHom (Spec.algebraMap R k) G n = n₀`.
The proof converts the residue normalizer equation to the all-test
transporter equation, uses the pullback-point correspondence to apply exact
Henselian transporter lifting over `R`, and converts the lifted transporter
back to the normalizer equation. Injectivity of the same point correspondence
turns its restriction equality into the displayed exact base-change equality.

`exists_henselian_normalizer` allows the prescribed residue automorphism
`σ₀` to be arbitrary. It first extends `σ₀` by
`automorphism_fieldBaseChange_surjective`, then applies the preceding theorem.
It produces both `n` and `σ`, preserving the normalizer equation and satisfying
both exact equalities `n_k = n₀` and `σ_k = σ₀`.

`henselianNormalizerLift` packages that proved existence as a chosen pair of
an integral section and an integral torus automorphism. Its subtype proof
records the actual normalizer equation and the exact recovery of both prescribed
residue values. It is defined by classical choice from
`exists_henselian_normalizer`, without any additional existence hypothesis.
The choice is not asserted to be canonical or unique.

This unit starts with a normalizing residue point. It does not construct a
normalizer lift through a reductive quotient, a Weyl reflection representative,
or a root-factor decomposition. Those residue geometry and radical comparison
steps, and the final depth-zero opposite-factor statement, remain separate
proof obligations.
