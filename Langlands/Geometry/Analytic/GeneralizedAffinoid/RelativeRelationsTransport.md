# Bounded coefficient transport through relative equation quotients

Author: Worker 56. This module constructs transport directly from the published
`RelativeRelations`, `GeneralizedTateAlgebra.RelativeAlgebra` and
`BoundedEquivalence.Definitions` APIs. Its namespace is
`Langlands.Analytic.PresentedAffinoidAlgebra.RelativeRelations`.

## Parameters and relation compatibility

Let K be an ultrametric normed field and let A, B and C be actual
`PresentedAffinoidAlgebra K` objects. Fix `m : ℕ` and
`s : PositivePolyradius (Fin m)`. Put

\[
T_A=A\{s^{-1}U\},\qquad
I_E=\overline{(E)},\qquad Q(A,E)=T_A/I_E,
\]

where the Lean objects are `GeneralizedTateAlgebra s A`,
`RelativeRelations.ideal K A s E` and
`RelativeRelations.QuotientAlgebra K A s E`. The last object has the actual
quotient norm imported from `RelativeRelations`.

For a supplied bounded K-algebra map `φ : BoundedAlgHom K A B`, let
`T(φ) = mapCoefficientsAlgHom s φ`. It applies φ to every series coefficient.
`MapsRelations K s φ E F : Prop` means

\[
\forall f\in E,\quad T(\varphi)(f)\in I_F .
\]

This is a condition on the input equations and the actual coefficient map;
it does not supply a quotient map or an output equivalence.
`mapsRelations_of_mapsTo` proves it when `T(φ)` sends E into F itself,
using inclusion of F in its closed generated ideal.

`mapsRelations_ideal` proves that the condition also sends all of `I_E`
into `I_F`. The proof composes `T(φ)` with the target quotient map. This
bounded composite vanishes on E by the target's exact kernel theorem,
so `RelativeRelations.annihilates_ideal` makes it vanish on `I_E`.
The same exact kernel theorem converts vanishing back to membership in `I_F`.
`mapsRelations_id` uses generator inclusion and coefficientwise identity.
`mapsRelations_comp` uses preservation of the entire intermediate closed
ideal and coefficientwise composition.

## Descended maps and their laws

`transport K s E F φ hφ` is `RelativeRelations.descend` of
`(quotientMap K B s F).comp (mapCoefficientsAlgHom s φ)`. Thus

\[
\overline T(\varphi)([f])=[T(\varphi)(f)].
\]

`transport_quotientMap` is this representative formula, definitionally;
`transport_comp_quotientMap` gives the equality of bounded maps.
`transport_baseMap` applies coefficientwise naturality for constant series,
and `transport_newCoordinate` applies the coefficient map's variable formula.
Consequently the base coefficient a maps to φ(a), and every new variable
keeps its label.

`eq_transport` proves uniqueness of a bounded map with this representative
formula, using quotient surjectivity through `RelativeRelations.hom_ext`.
`transport_id` and `transport_comp` apply the same extensionality and the
coefficientwise identity and composition laws. These are equalities of actual
bounded K-algebra maps between the quotient carriers. The proofs of relation
compatibility have no effect on the map.

## Norm bounds

`norm_transport_le` transfers every supplied nonnegative coefficient bound:

\[
c\geq0,\quad \|\varphi(a)\|\leq c\|a\|\ \text{for every }a
\quad\Longrightarrow\quad
\|\overline T(\varphi)(x)\|\leq c\|x\|.
\]

For `c > 0`, the coefficientwise series map has the same bound by
`norm_mapCoefficientsAlgHom_le`, and the target quotient map is contractive.
`RelativeRelations.norm_descend_le` transfers that bound to the source
quotient norm, using representatives with arbitrarily small norm excess.
For `c = 0`, choose any source representative. The coefficientwise bound
and target contraction already force its image to have norm zero.
This covers the nonnegative endpoint without assuming the quotient is
nontrivial. `norm_transport_le_of_contractive` specializes to `c = 1`.

## Supplied base equivalences

For a supplied `e : BoundedAlgEquiv K A B`, assume `MapsRelations` for e
from E to F and for `e.symm` from F to E. `transportEquiv` packages the
two constructed descended maps using `BoundedAlgEquiv.ofHomInv`.
Both inverse identities are proved on arbitrary series representatives.
Coefficientwise composition turns each composite into the coefficient map
of a base composite, and the supplied base equivalence's inverse identities
turn that composite into the identity. No inverse on the quotients is assumed.

`transportEquiv_apply` and `transportEquiv_symm_apply` identify the two maps.
`norm_transportEquiv_le` and `norm_transportEquiv_symm_le` transfer every
supplied nonnegative forward and inverse bound separately. A general bounded
base equivalence need not preserve norms.

If `‖e a‖ = ‖a‖` for all a, its inverse preserves norms as well, by applying
that equality to `e.symm b`. Both descended maps are then contractive.
Their inverse identities give equality of the actual quotient norms
(`norm_transportEquiv`). `isometry_transportEquiv` obtains this hypothesis
from an isometric base equivalence and uses additive-map norm preservation
to prove that the quotient equivalence is an isometry.

## Scope

No declaration assumes completeness of K. The constructions retain empty old
and new variable blocks, arbitrary positive real radii, nonproper ideals,
zero coefficient algebras or equation quotients, and trivial valuations.
They start with a supplied bounded base map or bounded base equivalence and
explicit relation compatibility. The module does not construct equivalences
between arbitrary presentations or compare the scalar `Adjoin.algebra` with
the relative quotient. It does not construct analytic domains, sheaves or
etale sites, and does not complete the broader analytic geometry task.

## Original convention and derived provenance

Berkovich, *Non-Archimedean analytic spaces*, Trieste lectures (2009),
Definition 2.1.6(i), printed/PDF page 8, defines relative series by weighted
coefficient decay and their maximum norm. In finitely many variables this
decay agrees with the cofinite exponent decay used by the imported
`GeneralizedTateAlgebra`. Part (ii) defines an A-affinoid algebra through an
admissible epimorphism from such series. The page was read directly.

This module's coefficient transport, compatibility with closed generated
ideals, exact quotient norm bounds and transport of supplied base equivalences
are internal derived infrastructure. They follow from the imported concrete
coefficientwise maps, bounded quotient descent and bounded equivalence
constructor; they are not quoted as assertions of that numbered definition.
The source works with complete ground fields. The normed constructions here
also work for incomplete K; this does not assert an A-affinoid or k-affinoid
classification of their quotients.

Registered original: `berkovich-2009-trieste-analytic-spaces`, SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
Retained file:
`/home/taskhub/central-library/Berkovich--Non-archimedean analytic spaces (Trieste lectures)--2009/Berkovich--Non-archimedean analytic spaces (Trieste lectures)--2009.pdf`.
