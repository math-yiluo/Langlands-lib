# Distinct tangent characters at geometric points

This module defines the distinct-character condition on the actual tangent
representation of a finite-coordinate formal module with an order action.
It provides the geometric tangent condition needed for Drinfeld's definition
of a special formal `O_D`-module and proves its preservation under coefficient
extension and order-linear isomorphisms.

The original source is Drinfeld, *Coverings of p-adic symmetric regions*
(1976), section 2 A, printed p.109, the definition immediately following
quasi-isogenies. It is registered as
`drinfeld-1976-coverings-p-adic-symmetric-regions`, SHA256
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.
There Drinfeld restricts the tangent representation to the maximal
unramified subring of the maximal order and requires a sum of `d` different
characters at every geometric point. The coordinate representation and
transport proofs below are derived infrastructure implementing that
condition; their API is not attributed to the source.

For a formal `O`-linear map `f` and a ring map `φ : R →+* K`,
`ModuleLaw.Hom.fiberTangent` first maps every formal coefficient by `φ` and
then differentiates. It is a `K`-linear map between coordinate tangent
modules. Its identity, zero, addition and composition laws follow from
coefficient mapping and the chain rule proved in `Tangent`.
`ModuleLaw.Iso.fiberTangent` uses the differentiated actual inverse to give
a linear equivalence.

For `E : OrderAction A M`, `OrderAction.fiberTangent` is the unital ring
homomorphism from the possibly noncommutative ring `A` to endomorphisms of
the tangent module `σ → K`. Each matrix entry is the image under `φ` of the
corresponding actual linear coefficient of the formal endomorphism.
`fiberTangent_scalar` proves that restriction along `O → A` acts by the
scalar `φ (algebraMap O R a)`. No `O`-algebra structure on `K` needs to be
chosen: the composite ring map specifies this scalar. The equality
`fiberTangent_map` identifies a fibre after an `O`-algebra coefficient
extension `θ : R →ₐ[O] S` with the fibre at `φ.comp θ.toRingHom`.
`OrderAction.Hom.fiberTangent_commutes` differentiates the actual formal
commutation equation to obtain the intertwining equation.

For a commutative ring `C`, a ring homomorphism `ι : C →+* A`, and a
nonnegative integer `d`, `TangentCharacterDecomposition` contains:

- `d` ring characters from `C` to `K`, indexed injectively by `Fin d`;
- a `K`-linear equivalence from the actual coordinate tangent module to
  `Fin d → K`;
- the equation that this equivalence diagonalizes the restricted actual
  tangent action, with the indexed characters as diagonal entries.

Over a field the theorem `TangentCharacterDecomposition.finrank` gives
tangent dimension `d` using this equivalence and the dimension of `Fin d → K`.
The theorem `character_scalar` also forces each character to have the
natural value on any `c : C` whose image is an `O`-scalar. Its proof evaluates
the diagonalizing equation on the inverse image of a coordinate unit vector,
uses the scalar action theorem, and reads that coordinate.

`HasGeometricTangentCharacters` is a proposition requiring such a
decomposition at every ring map from `R` to an algebraically closed field
`L`. It is universe-polymorphic in the universe of `L`, independently of
the base ring and the acting rings. Each instance quantifies over all
algebraically closed fields in that universe; no single small field universe
is asserted to encode every possible geometric point.

`TangentCharacterDecomposition.map` retains the characters and diagonalizing
coordinates under the composite-fibre equality. The corresponding theorem
`HasGeometricTangentCharacters.map` applies this to each geometric point of
the extended base. The construction `TangentCharacterDecomposition.ofIso`
composes the original diagonalizing coordinates with the derivative of the
inverse order-linear isomorphism. The intertwining equation for that inverse
proves diagonalization. `HasGeometricTangentCharacters.ofIso` and
`iff_of_iso` establish preservation and equivalence of the geometric
condition.

The rings remain general in this unit. In particular, `ι` is a ring map;
the module supplies neither its injectivity nor its identification with the
maximal unramified subring of an actual maximal order. The formal groups
have global finite coordinates, whereas Drinfeld also allows groups glued
over localizations. Height, the local-field and division-algebra
specialization, the framing object, the moduli functor, and representability
require further constructions. This module alone does not define a full
special formal `O_D`-module.
