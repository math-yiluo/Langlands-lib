# Big-cell gluing from laws of the positive cell factors

This internal derived criterion sharpens the simple-root gluing criterion of
`Langlands.GroupScheme.Reductive.LocalSplitSimpleGeneratorRelations`. That criterion
has a hypothesis on right translation of big-cell points by the simple-root points
`u_a(c)`. This module replaces it with a hypothesis that only involves the positive
cell factors. Every law

`(∏ₖ u_{pos k}(w k)) · u_a(c) = ∏ₖ u_{pos k}(z k)`

of the positive cell factor of the Weyl family of `G` must also hold for `H`. The
base ring is arbitrary and may have nilpotents. The negative simple relations
remain as a hypothesis, unchanged.

## Statement

`LocalSplitPositiveLawIsomorphismStatement.{u}` has the same data and hypotheses as
`LocalSplitSimpleRootRelationIsomorphismStatement`, except for the first relation
hypothesis:

- a commutative ring `R`, a finite type `I` with decidable equality, and a type `J`,
  all in universe `u`;
- reductive group schemes `G`, `H` over `Spec R`, with instance binders `IsAffineHom`
  for their structure morphisms;
- coordinate split tori `i : T_I → G` and `i' : T_I → H`, both maximal on every
  residue-field fibre (`IsFibrewiseMaximalTorus`);
- one coordinate root datum `P : RootDatum J (I → ℤ) (I → ℤ)` that is a fibrewise
  root datum (`IsFibrewiseRootDatumOf`) for `i` in `G` and for `i'` in `H`;
- a base `b` of `P` and a choice `W` of a `SimpleWord P b α` for every root `α`;
- families `u : J → (𝔾ₐ ⟶ G)` and `u' : J → (𝔾ₐ ⟶ H)`. For every simple root `a`,
  `u a` is a root parametrization of `i` for `P.root a`, and `rootWeylPoint P u a`
  is a Weyl point of `i` acting by `P.reflection a`. The same holds for `u'` and
  `i'`;
- enumerations `neg : Fin m ≃ {α // ¬ b.IsPos α}` and `pos : Fin n ≃ {α // b.IsPos α}`
  of the non-positive and the positive roots.

Write `u_W = weylFamily P W u` and `u'_W = weylFamily P W u'`. Let
`Ω = cellMap i u_W neg pos` and `Ω' = cellMap i' u'_W neg pos` be the two big-cell
maps. The two hypotheses concern every commutative local ring `A : Type u` with
separably closed residue field, every structure map `s : Spec A → Spec R` and every
simple root `a ∈ b.support`:

- **positive-factor laws:** for every global function `c` and all coordinate
  vectors `w, z : Fin n → Γ(Spec A, ⊤)`, if
  `orderedProduct u_W pos w · u_a(c) = orderedProduct u_W pos z` in `G`, then
  `orderedProduct u'_W pos w · u'_a(c) = orderedProduct u'_W pos z` in `H`. Here
  `u_a(c)` is the point of the simple-root datum `u a` itself, and
  `orderedProduct u_W pos w` is `∏ₖ u_W(pos k)(w k)` in the order of `pos`;
- **negative simple relations:** for all cell-source points `x`, `y` over `s`, if
  `Ω(x) · u_{-a}(-1) = Ω(y)`, then `Ω'(x) · u'_{-a}(-1) = Ω'(y)`, where `u_{-a}`
  means `u (P.reflectionPerm a a)`.

The conclusion is an isomorphism `ψ : G ≅ H` with `Ω ≫ ψ = Ω'`. The module proves
this proposition at full universe as `localSplitPositiveLawIsomorphism`.

The namespace `LocalSplitCell` also contains:

- `comp_cellMap_mul_of_orderedProduct_mul`: if `(∏ₖ u_{pos k}(posCoord x k)) · g`
  equals `∏ₖ u_{pos k}(z k)`, then `Ω(x) · g` is the cell point with the negative and
  torus coordinates of `x` and positive coordinates `z`. This holds for any family,
  any enumerations and any test object;
- `extendFamily v u` and `extendChar χ ch`: the family `u` and its characters `ch`
  extended to `Option J` by one further parametrization `v` with character `χ`;
- `exists_orderedProduct_mul_rootPoint_eq_pos_of_equivariant`: under the hypotheses
  of the imported `exists_orderedProduct_mul_rootPoint_eq_pos`, the same conclusion
  for right multiplication by a point of any parametrization `v` on which the torus
  acts through a character `χ` with `⟨χ, ν⟩ > 0`. `v` need not be a member of the
  family;
- `comp_cellMap_mul_rootPoint_transfer`: under the same hypotheses, if every law
  `(∏ₖ u_{pos k}(w k)) · v(c) = ∏ₖ u_{pos k}(z k)` over a local test ring also holds
  for `u'` and `v'` in `H`, then every relation `Ω(x) · v(c) = Ω(y)` gives
  `Ω'(x) · v'(c) = Ω'(y)`;
- `PositiveLawRelations b W u u' pos`: the positive-factor law hypothesis above, for
  an arbitrary enumeration `pos : Fin n → J`;
- `simpleRootRelations_of_positiveLawRelations`: for `G` reductive with the fibrewise
  data above, the positive-factor laws give the hypothesis
  `SimpleRootRelations` of the imported module.

## Proof

**Cell points.** By `comp_cellMap`, `Ω(x) = A · τ · B` with `A` the negative factor,
`τ` the torus point and `B = ∏ₖ u_{pos k}(posCoord x k)`. So `Ω(x) · g = A · τ · (B · g)`.
If `B · g = ∏ₖ u_{pos k}(z k)`, this is the cell point with coordinates
`(negCoord x, torusCoord x, z)` (`comp_cellMap_mul_of_orderedProduct_mul`).

**One further parametrization.** The imported
`exists_orderedProduct_mul_rootPoint_eq_pos` (module
`Langlands.GroupScheme.Reductive.LocalSplitPositiveCell`) treats right
multiplication by a point of a member of the family. Index the family by `Option J`,
with `v` at `none` (`extendFamily`), and extend the characters by `χ`
(`extendChar`). Torus equivariance of the extended family follows from that of `u`
and the hypothesis on `v`. On the indices `some α`, the extended family is `u`, so
the ordered products along `some ∘ e` are those of `u` along `e`
(`orderedProduct_extendFamily_some`). Its cell map along `some ∘ neg`, `some ∘ pos`
is therefore the original cell map (`cellMap_extendFamily_some`), which supplies the
open-immersion instance. The imported lemma with the index `none` gives
`exists_orderedProduct_mul_rootPoint_eq_pos_of_equivariant`.

**Transfer.** In `comp_cellMap_mul_rootPoint_transfer`, let `Ω(x) · v(c) = Ω(y)`.
The previous step gives `z` with `B · v(c) = ∏ₖ u_{pos k}(z k)` for the positive factor
`B` of `x`. The first step then gives `Ω(x) · v(c) = Ω(x')`, with
`x' = (negCoord x, torusCoord x, z)`. Since `Ω` is an open immersion, it is a
monomorphism, so `y = x'`. The law hypothesis gives
`B' · v'(c) = ∏ₖ u'_{pos k}(z k)` in `H` for the positive factor `B'` of `x` under `Ω'`.
The first step for `H` gives `Ω'(x) · v'(c) = Ω'(x') = Ω'(y)`.

**Weyl families.** The imported `isRootParametrization_weylFamily` makes every member
of `u_W` a root parametrization for its root. Hence `u_W` is torus equivariant with
characters `ch α = P.root α`, and `Ω` is an open immersion by the imported
`LocalSplitBigCell.isOpenImmersion_cellMap`. The imported `exists_cocharacter_of_base`
gives `ν` pairing positively with the positive roots and negatively with the other
roots. A simple root `a` is positive (Mathlib's
`RootPairing.Base.isPos_of_mem_support`), and `u a` is equivariant through
`P.root a` by its root-parametrization hypothesis. So the transfer lemma, applied
with `v = u a` and `v' = u' a`, turns the law hypothesis into `SimpleRootRelations`.
This is `simpleRootRelations_of_positiveLawRelations`. The proposition follows from
the imported `localSplitSimpleRootRelationIsomorphism`.

## Provenance and scope

This is an internal derived criterion for the Isomorphism Theorem over an arbitrary
local ring. It follows the strategy of the proofs of the Isomorphism and Isogeny
Theorems. There, the group law on the product `U_{Φ⁺}` of the positive root groups
is described by commutation relations with structure constants. These constants
are then shown to depend only on the pinned root datum (B. Conrad, *Reductive group
schemes*, Theorem 5.1.13 and Lemma 6.2.8; SGA 3, Exp. XXIII, 3.1–3.4). The argument
above is an explicit construction of this module.

The criterion does not verify the positive-factor laws or the negative simple
relations for any pair of groups. Verifying the laws amounts to comparing the
commutation relations of the positive root groups of the two Weyl families, which
is the content of Conrad's Lemma 6.2.8; this module does not do so. The criterion
does not construct Weyl-normalized simple-root data. It does not prove the local
split Isomorphism Theorem.
