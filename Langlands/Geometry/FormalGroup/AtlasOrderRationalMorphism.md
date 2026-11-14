# Full-order rational formal atlas maps

This is an internal construction from `AtlasRationalMorphism`,
`AtlasOrderMorphism` and the coordinate `OrderRationalMorphism` API. It restricts
global rational atlas maps by formal commutation on every chart. The algebraic
closure and inverse constructions follow from those existing formal maps and
their equations; no new original-literature assertion is used.

## Parameters and the centralizer

O and R are commutative rings, R is an O-algebra, D is a possibly noncommutative
ring with an O-algebra structure, and F is a field with an O-algebra structure.
The coordinate types are finite. The atlases X and Y carry actual `OrderAction`
structures E and E', and their principal-open generator sets have a supplied
equality `h`. Coefficient test algebras are `CommAlgCat.{v} R`, in the universe
of R. No maximality or division-algebra classification of D is needed here.

`rationalHomSubmodule F E E' h` is the F-submodule of
`BasicAtlas.RationalHom F X Y h` consisting of maps f for which every usable
test chart satisfies

`f_b compose E_b(a) = E'_b(a) compose f_b`

for every a in D. Here f_b is actual rational formal chart evaluation, and the
actions are the actual coefficient-extended integral formal actions included
in coordinate rational Hom. Closure under zero, addition and F-scalars uses
linearity of chart evaluation and bilinearity of coordinate composition.
`OrderAction.RationalHom` is the carrier of this submodule. It inherits an
additive commutative group and F-module. `toLinearMap` forgets the commutation
condition and is injective; `ext` proves equality from equality of the underlying
global tensor maps.

## Evaluation and composition

`onChart` constructs an actual coordinate `OrderAction.RationalHom` from a
global full-order rational map. `commutes` exposes its formal commutation
equation, and `onChartLinear` packages evaluation as an F-linear map into the
coordinate centralizer. The underlying global map still satisfies both formal
coefficient naturality and transition equations from `AtlasRationalMorphism`.

`ofHom` includes every actual integral full-order atlas homomorphism.
`id` and `comp` use the rational identity and composition of the underlying
atlas maps. To prove closure under composition, the construction evaluates on
each chart, uses preservation of composition, and applies closure of the
coordinate full-order centralizer. Forgetting gives exactly the inherited
rational maps (`ofHom_val`, `id_val`, `comp_val`).

Equality in the ambient tensor Hom proves both identity laws, associativity,
additive and scalar bilinearity, zero laws and `ofHom` compatibility with
identity and composition. `compLinear` packages F-bilinearity. Endomorphisms
of one order-equipped atlas form a ring with multiplication given by formal
composition and unit the rational identity. `onChart_id`, `onChart_comp` and
`onChart_ofHom` prove compatibility with the corresponding coordinate
full-order constructions.

## Quasi-isogenies and inverse equivariance

For this part O is a domain and F its fraction field.
`OrderAction.QuasiIsogeny F E E' h` stores two full-order rational maps in
opposite directions, with both rational composition equations. Forgetting the
order gives the actual `BasicAtlas.QuasiIsogeny` (`toAtlasQuasiIsogeny`).

`inverse_commutes` starts with an underlying atlas quasi-isogeny whose forward
map belongs to the full-order centralizer and proves that its inverse belongs
to the opposite centralizer. On each chart it applies the existing coordinate
inverse-equivariance theorem to the actual chart quasi-isogeny. That theorem
uses associativity, the forward commutation equation and the two inverse laws;
no additional inverse-equivariance hypothesis is imposed.
`ofAtlasQuasiIsogeny` thus upgrades an underlying quasi-isogeny using forward
commutation alone. Forgetting this upgrade recovers the original quasi-isogeny.

`refl`, `symm`, `trans` and `ofIso` give identity, inverse, composition and
inclusion of actual integral full-order atlas isomorphisms. The underlying
inverse-uniqueness theorem proves `inv_unique`; forward-map equality determines
the entire quasi-isogeny (`ext_hom`). Finally, `QuasiIsogeny.onChart` constructs
an actual coordinate full-order quasi-isogeny. It evaluates both maps, retains
their full-order equations and uses the underlying chart inverse laws.

## Scope

The centralizer lies inside the global tensor product of integral O-linear
atlas Hom. No equality with the tensor product of integral D-linear atlas Hom
is asserted. Covers must be equal, coefficient tests retain the base-ring
universe, and no identification with all locally rational maps is made.
General-refinement transport, rational local gluing, heights, framing triples,
polarizations, actions, levels and representability remain separate. There is
no representing object, universal object or classification input.
