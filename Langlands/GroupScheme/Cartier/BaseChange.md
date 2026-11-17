# Base change of actual relative homomorphisms and characters

Let `S` and `S'` be schemes in universe `u`, let `b : S' ⟶ S` be any morphism,
and let `G` and `H` be commutative group schemes over `S`. This module constructs
the natural isomorphism

`(Over.map b).op ⋙ Cartier.relativeHomFunctor G H ≅
 Cartier.relativeHomFunctor G_b H_b`.

Here `G_b` and `H_b` denote the published `CommGroupScheme.baseChange` objects.
The presheaves have values in `AddCommGrpCat.{u}` on the full category of
schemes over the indicated base. Restriction to `S'` means composition of a
test scheme's structure morphism with `b`. There is no flatness, finiteness,
normality, or local constancy premise.

`testBaseChangeAlongIso` lifts the published group-scheme isomorphism between
composite and iterated pullback to the commutative group-scheme category.
It identifies `G ×_S T` with `(G ×_S S') ×_{S'} T`.
The three projection lemmas specify its scheme maps.
`testBaseChangeAlongIso_inv_baseChangeProj` proves that these comparisons
commute with the actual restriction projections on test schemes, by checking
the two pullback projections.

`relativeHomBaseChangeEquiv` sends an actual homomorphism `χ : G_T ⟶ H_T`
to `e_G⁻¹ ≫ χ ≫ e_H`, where the `e` are the preceding comparisons.
Preadditivity makes this an additive equivalence; cancellation of the
comparison isomorphisms proves both inverse laws.
`relativeHomBaseChangeEquiv_restrict` proves its naturality. After the
published `relativeHom_ext`, the proof checks the two projections of
`H ×_S S'`: the projection to `H` uses `Cartier.restrict_fst` and naturality
of the comparison projections, and the projection to `S'` follows because
the homomorphisms are over the test scheme.
`relativeHomBaseChangeIso` bundles this into a natural isomorphism of the
actual abelian presheaves.

`charactersBaseChangeIso` specializes the construction to `H = Gm S`,
then applies the published relative-Hom target functor to
`Gm.commBaseChangeIso b`. It gives

`(Over.map b).op ⋙ Cartier.characters G ≅ Cartier.characters G_b`.

`charactersBaseChangeIso_hom_app_apply` states its map on each test scheme:
the preceding Hom equivalence followed by the base change of the canonical
`Gm` comparison. Naturality is already provided by the composed natural
isomorphisms.

This is a derived categorical construction from the imported actual Hom,
restriction, pullback coherence, and multiplicative-group definitions.
It provides no assertion that characters are locally constant or that a
local system admits a finite splitting cover.
