# Transport of actual formal atlases between equal scalar algebra structures

This derived unit transports formal module laws and actual principal-cover
atlases between two equal O-algebra structures on the same commutative ring R.
It retains the original coordinate data and proves identity and composition
laws for the transport.

## Provenance and scope

This is internal infrastructure derived from `ModuleLaw` and `BasicAtlas`,
using equality elimination in Lean. It claims no additional theorem from the
literature. The underlying atlas construction implements Drinfeld's convention
that formal groups may be glued over localizations; its source and scope are
documented in `BasicAtlas.md`. This unit resolves the type-level distinction
between equal scalar structures that occurs when comparing coefficient
extension with an independently supplied O-algebra structure.

O and R are arbitrary commutative rings. The coordinate type is finite, and the
principal cover may be infinite. Test algebras remain in universe v. The input
is an explicit equality between the two `Algebra O R` structures; no equality
is asserted for arbitrary scalar structures. This module constructs neither
coefficient extension along an arbitrary O-algebra homomorphism nor its
identity comparison. It supplies no acting-order extension, specialness or
height transport, varying-base moduli functor, framing or representability.

## Formal module laws

`ModuleLaw.reAlgebra M β e` starts with a formal O-module M for the algebra
structure α and returns one for β, given `e : α = β`. Its commutative formal
group law and its entire action homomorphism are the original data. Only the
natural tangent-action condition is transported, by eliminating e.
`reAlgebra_groupLaw` and `reAlgebra_action` record these literal preservation
properties. `reAlgebra_refl` returns M, and `reAlgebra_trans` equates successive
transport with transport along the composite equality. The latter proof
eliminates both equalities and closes by reflexivity.

## Actual atlases

`BasicAtlas.localizationAlgebra_eq` derives equality of the induced O-algebra
structures on R[1/a] from equality of those on R. Its proof eliminates the
given equality.

`BasicAtlas.reAlgebra X β e` retains X's principal generators and their covering
proof. Each chart is transported with `ModuleLaw.reAlgebra` using the
localization algebra equality. Each actual formal transition isomorphism is
transported by equality elimination. The identity, cocycle and coefficient
naturality laws follow from X's original laws, using extensionality on formal
maps for the first two. Thus both formal maps of a transition and both inverse
equations remain present.

`reAlgebra_opens`, `reAlgebra_chart_groupLaw` and `reAlgebra_chart_action` state
that the generators, chart group laws and every chart scalar action are
unchanged. `reAlgebra_transition_coordinates` and
`reAlgebra_transition_inv_coordinates` identify the forward and inverse formal
coordinate series on every common test algebra; both are proved by eliminating
the algebra equality. The atlas-level `reAlgebra_refl` is reflexivity, and
`reAlgebra_trans` follows by eliminating both equalities and reflexivity.
