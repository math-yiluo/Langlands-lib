# Concrete limits of smooth representations over small diagrams

Module `Langlands.Representation.Category.ConcreteSmoothLimits`.

## Content

For a diagram `F : J ⥤ SmoothRep R G` indexed by a small category `J : Type` (coefficients in a
commutative ring `R`, `G` a topological group), this module constructs an explicit limit and
extracts two properties valid for every limit cone.

- `familyRepresentation F`: the componentwise action of `G` on all families `∀ j, F.obj j`.
- `compatibleFamilies F`: the subrepresentation of families `x` with
  `hom (F.map f) (x i) = x j` for every morphism `f : i ⟶ j`.
- `smoothCompatibleFamilies F`: its intersection with the smooth vectors of the family
  representation, i.e. compatible families fixed by some open subgroup.
- `concreteLimit F`, `concreteLimitπ F j`, `concreteLimitCone F`: the smooth representation on
  smooth compatible families and its coordinate projections.
- `concreteLimitIsLimit F`: this cone is a limit cone. The lift of a cone `s` sends `v` to the
  family `j ↦ s.π.app j v`; it is compatible by naturality of `s.π`, and smooth because an open
  subgroup fixing `v` fixes every coordinate by equivariance.
- `eq_zero_of_isLimit`: in any limit cone `c` the projections are jointly injective: a vector
  of `c.pt` whose projections all vanish is zero.
- `exists_eq_of_isLimit`: in any limit cone `c`, a compatible family `y` all of whose
  coordinates are fixed by one open subgroup `K` is the family of projections of a vector of
  `c.pt`.
- `exists_fixed_eq_of_isLimit`: the same, with the vector of `c.pt` itself fixed by `K`.
- `discreteOp_map_apply`: for a diagram indexed by `(Discrete ι)ᵒᵖ` (the shape of the dual of a
  coproduct), every family of vectors is compatible, since the only morphisms are identities.

## Proof

Both extraction results transport along the canonical isomorphism
`IsLimit.conePointUniqueUpToIso` from `c.pt` to the concrete limit, which commutes with the
projections (`IsLimit.conePointUniqueUpToIso_hom_comp` and `_inv_comp`). Injectivity holds in the
concrete limit because a family is determined by its coordinates (`concreteLimit_ext`);
surjectivity holds because the family `y` itself, being compatible and fixed by `K`, is a vector
of the concrete limit. For `exists_fixed_eq_of_isLimit`, if `x` has projections `y` and
`k ∈ K`, then `k x - x` has projections `k (y j) - y j = 0` by equivariance, so `k x = x` by
joint injectivity. For `discreteOp_map_apply`, a morphism `f : i ⟶ j` of `(Discrete ι)ᵒᵖ`
forces `i = j` (`Discrete.eq_of_hom`), then `f = 𝟙 i` because hom-sets of a discrete category are
subsingletons, and `H.map (𝟙 i) = 𝟙`.

## Provenance

This is standard category-theoretic infrastructure, internal to the project; it is not a
statement from the literature. It is used to read off concrete consequences from the
preservation of countable products by a Jacquet functor in the proof of Renard VI.9.6.
