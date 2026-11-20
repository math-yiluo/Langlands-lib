# Weyl transport of rootwise data

This internal derived support module, in namespace
`Langlands.GroupScheme.MaximalSplitSubgroup`, is part of the proof of
`MaximalSplitSubgroupStatement` (Borel–Tits 1965, Theorem 7.2). It records how a
rational point normalizing a torus moves rootwise data around. Step 3 of the proof
of Conrad–Gabber–Prasad, *Pseudo-reductive groups*, Theorem C.2.29, uses this:
the points `n_a` act on the characters by the reflections `r_a`, and weights are
stable under the Weyl group they generate.

Throughout, `K` is a field, `T` is a commutative group scheme over `Spec K` (with
its character and cocharacter lattices and the pairing `latticePairing T`), `H` is a
group scheme over `Spec K`, and `t : T.toGrp ⟶ H` is a homomorphism. A rational
point of `H` is a morphism `Over.mk (𝟙 (Spec K)) ⟶ H.X`. The Library predicate
`IsNormalizingPoint t n σ` says that conjugation by the rational point `n`
preserves `t` and acts on `T` through the automorphism `σ`.

## Declarations

- `HasWeylInversion t χ` (definition): there are an automorphism `σ` of `T` and a
  rational point `n` of `H` such that `IsNormalizingPoint t n σ`, `σ.hom ≫ χ = -χ`,
  and `ξ ≫ σ.hom = ξ` for every cocharacter `ξ` with `⟨χ, ξ⟩ = 0`.
- `latticePairing_comp`: for an endomorphism `f` of `T`,
  `⟨f ≫ χ, ξ⟩ = ⟨χ, ξ ≫ f⟩`.
- `HasWeylInversion.transport`: if `χ` has a Weyl inversion and
  `IsNormalizingPoint t m τ`, then `τ.inv ≫ χ` has a Weyl inversion.
- `hasWeylInversion_of_reflection`: if `⟨a, ν⟩ = 2` and a rational point `n`
  normalizes `t` through the lattice reflection `latticeReflectionIso a ν hpair`,
  then `a` has a Weyl inversion.
- `torusGrpIso σ`: an automorphism `σ` of `T` as an automorphism of the underlying
  group scheme `T.toGrp`, with `hom = CommGroupScheme.groupHom σ.hom`.
- `HasWeylInversion.exists_transporter` (`H.X.hom` affine): a Weyl inversion of
  `χ` gives the rootwise Weyl datum required by the hypothesis `hweyl` of
  `RootwiseWeyl.isConnectedReductive_of_rootwiseWeyl`. That datum is an automorphism
  `c` of `T.toGrp` and an affine point `n` of `H` such that `c` turns `χ` into `-χ`,
  `c` fixes every cocharacter orthogonal to `χ`, and `n` is a transporter from
  `c.hom ≫ t` to `t`.
- `iso_inv_comp_ne_zero_iff`: `τ.inv ≫ χ ≠ 0 ↔ χ ≠ 0`.

Every remaining declaration, from `basePointAdjoint_injective` through
`IsWeylLineRoot.reflection`, assumes in addition that `H` is affine
(`[IsAffineHom H.X.hom]`, a section variable at Lean line 97). The Library's
`weightSpace` and `roots` are built from the adjoint action of the affine group
scheme `H` on its Lie algebra, so the definition `IsWeylLineRoot` and all the
statements below are only formed for affine `H`.

- `basePointAdjoint_injective`: the adjoint action of a rational point on the Lie
  algebra is injective.
- `mem_roots_iff_of_isNormalizingPoint`: if `IsNormalizingPoint t n τ`, then
  `τ.inv ≫ χ ∈ roots t ↔ χ ∈ roots t`.
- `finrank_weightSpace_of_isNormalizingPoint`: under the same hypothesis the weight
  spaces of `τ.inv ≫ χ` and `χ` have the same dimension over `K`.
- `IsWeylLineRoot t χ` (definition): `χ` is a root of `t`, its weight space has
  dimension one, and `χ` has a Weyl inversion.
- `IsWeylLineRoot.transport`: if `IsWeylLineRoot t χ` and `IsNormalizingPoint t m τ`,
  then `IsWeylLineRoot t (τ.inv ≫ χ)`.
- `IsWeylLineRoot.reflection`: if `IsWeylLineRoot t χ`, `⟨a, ν⟩ = 2`, and a rational
  point normalizes `t` through `latticeReflectionIso a ν hpair`, then
  `IsWeylLineRoot t (χ - ⟨χ, ν⟩ • a)`.

## Proofs

`latticePairing_comp` unfolds the pairing (composition of a cocharacter with a
character) and reassociates.

`HasWeylInversion.transport`: let `σ, n` invert `χ`. The point `m * n * m⁻¹`
normalizes `t` through the automorphism with `hom = τ.inv ≫ σ.hom ≫ τ.hom`, by the
Library's `IsNormalizingPoint.mul` and `IsNormalizingPoint.inv`. Composing,
`(τ.inv ≫ σ.hom ≫ τ.hom) ≫ (τ.inv ≫ χ) = τ.inv ≫ σ.hom ≫ χ = -(τ.inv ≫ χ)`. If
`⟨τ.inv ≫ χ, ξ⟩ = 0` then `⟨χ, ξ ≫ τ.inv⟩ = 0` by `latticePairing_comp`. So `σ`
fixes `ξ ≫ τ.inv`, and hence `ξ ≫ τ.inv ≫ σ.hom ≫ τ.hom = ξ ≫ τ.inv ≫ τ.hom = ξ`.

`hasWeylInversion_of_reflection` takes the reflection itself. It uses the companion
module `MaximalSplitRankOneRelation`'s `reflection_comp_root` (the reflection sends
`a` to `-a`) and `cocharacter_comp_reflection` (it moves a cocharacter `ξ` by
`⟨a, ξ⟩ • ν`).

`HasWeylInversion.exists_transporter` takes `c = torusGrpIso σ` and the affine point
`(Lie.affineSelfTestIso K).hom ≫ n`. The two lattice conditions are the images of
the corresponding conditions under `CommGroupScheme.groupHom`. The transporter
property is the Library's `IsNormalizingPoint.isTransporter`, restricted along the
identification of the base test object.

`basePointAdjoint_injective`: `basePointAdjoint n⁻¹` is a left inverse, by the
Library's `basePointAdjoint_inv_mul`.

`mem_roots_iff_of_isNormalizingPoint` combines `iso_inv_comp_ne_zero_iff` with the
Library's `weightSpace_eq_bot_iff_of_isNormalizingPoint`.
`finrank_weightSpace_of_isNormalizingPoint`: by `IsNormalizingPoint.map_weightSpace`
the weight space of `τ.inv ≫ χ` is the image of the weight space of `χ` under the
injective linear map `basePointAdjoint n`.

`IsWeylLineRoot.transport` combines the three transport statements.
`IsWeylLineRoot.reflection` rewrites `χ - ⟨χ, ν⟩ • a` as
`(latticeReflectionIso a ν hpair).inv ≫ χ`
(`reflection_inv_comp_character`, from `MaximalSplitRankOneRelation`) and applies
`IsWeylLineRoot.transport`.

## Provenance

Derived. These are the elementary facts behind CGP Theorem C.2.29, Step 3 (printed
pp. 627–628): the points `n_a` normalize `S` and act on `X(S)` by the reflection
`r_a`, and the set of weights is stable under the Weyl group they generate. The
predicates `HasWeylInversion` and `IsWeylLineRoot` are local packagings for the
rootwise hypothesis of the companion reductivity criterion
`RootwiseWeyl.isConnectedReductive_of_rootwiseWeyl`. They state no more than their
definitions.
