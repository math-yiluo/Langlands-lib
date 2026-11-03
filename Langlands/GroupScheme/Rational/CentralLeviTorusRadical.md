# Central Levi tori and the solvable radical

This internally derived construction works over every field `k : Type u`.
Let `l : L ⟶ P` be an actual rational Levi subgroup, let `rR : R ⟶ P`
represent a ground-field solvable radical, and let `a : A.toGrp ⟶ L`
be a closed central torus, with `A` an actual commutative group scheme.
Then the all-test range of `a ≫ l` is contained in the range of `rR`.
The definition `IsRationalLeviSubgroup.centralTorusRadicalFactor`
constructs the unique group-scheme map `A.toGrp ⟶ R` whose composite
with `rR` is `a ≫ l`. It is a closed subgroup inclusion. The field need
not be perfect and the torus need not be split.

The statement uses the published rational Levi predicate, including its
actual multiplication isomorphism with a represented geometric unipotent
radical. No parabolic or minimal-parabolic hypothesis on `P` is needed
for this consequence. Only the ground-field greatest-subgroup property
of the specified solvable radical is used.

## Retraction geometry and the radical lift

Over any base scheme, suppose multiplication `L × U ⟶ P` from `l` and
`r : U ⟶ P` is an isomorphism and the all-test range of `r` is normal.
The published `leviRetraction l r hn : P ⟶ L` has underlying scheme map
equal to the inverse multiplication isomorphism followed by the first
product projection. Thus `smooth_leviRetraction` proves it is smooth
if `U` is smooth, and `geometricallyConnected_leviRetraction` proves
it is geometrically connected if `U` is geometrically connected.

`radical_comp_leviRetraction` proves that `r` has trivial composite
with this projection. For any actual homomorphism `a : A ⟶ L`,
`leviPreimageRadicalLift` is the pullback lift from `U` to the existing
`SubgroupPreimage.groupScheme q a`, with coordinates `r` and the
trivial homomorphism. Its composites with the two projections are
respectively `r` and the trivial homomorphism.

For each test scheme `T`, `isSolvable_points_leviPreimage` assumes that
the point groups `U(T)` and `A(T)` are solvable and proves solvability
of the pullback point group. The exact all-test kernel theorem for `q`
puts the kernel of the pullback projection to `A(T)` inside the image
of `U(T)` under the constructed radical lift. Mathlib's
`Group.isSolvable_of_ker_le_range` gives the conclusion. Surjectivity
of the map on `T`-points is not a premise.

## Radical containment and the actual factor

`IsRationalLeviSubgroup.range_centralTorus_le_solvableRadical`
chooses the represented geometric unipotent radical supplied by `l`.
It is smooth and connected, and is affine because it is closed in
the affine group `P`. The published geometric connectedness theorem
for connected finite-type groups applies. Therefore the actual
retraction `q : P ⟶ L` is smooth and geometrically connected.

Form the actual pullback `H = P ×[L] A`, using the existing inverse-image
construction. It is closed in `P`. Its projection to `A` is smooth and
geometrically connected by base change. Since a torus is smooth and
connected, `H` is smooth and connected. Centrality of `a` makes its
all-test range normal in `L`, so its inverse image is normal in `P`.

The published `isSolvable_points_of_isUnipotent` proves solvability of
every point group of the affine finite-type unipotent radical.
Commutativity gives solvability of every point group of `A`. The preceding
pullback lemma therefore proves solvability over the algebraic-closure
test scheme, and the published comparison with geometric points proves
`IsSolvableGroupScheme H`. The greatest-subgroup property of `rR`
puts the range of `H ⟶ P` in the range of `rR`.
Finally, `l ≫ q = 𝟙 L` puts the all-test range of `a ≫ l` in this
inverse image, proving the claimed containment.

The definition `centralTorusRadicalFactor` applies the published
represented-subgroup `factorHom` to this proved containment. Its
compatibility theorem is `centralTorusRadicalFactor_comp`. Uniqueness
follows from monicity of the closed inclusion `rR`, or from the
existing `factorHom_unique`. Closedness of the factor follows because
its composite is the composite of the two closed embeddings `a` and `l`.
The construction does not assert that the torus is central in `R`.

## Provenance and scope

The source motivation is Borel–Tits, *Groupes réductifs* (1965),
Corollary 4.16, proof of (i) implies (ii), printed pp.91–92
(PDF pp.38–39): after identifying the refined parabolic with the
minimal parabolic, the extended split torus lies in the solvable
radical. This module supplies the central-Levi-torus containment
step through an actual pullback and the published retraction.
Its proof route and the general formulation without parabolicity
are internal derivations from the imported definitions and theorems.
The source is registered as `borel-tits-1965-groupes-reductifs`,
SHA-256 `ec6674ba292deaadd77a449f4bad3750db79c0b87b117a892ef6b09bb16357ad`.

This module does not construct the compatible parabolic refinement,
show that a maximal split extension is central in the resulting Levi,
or prove `MinimalParabolicLeviCentralizerStatement`. Those geometric
steps remain separate obligations.
