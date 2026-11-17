# Effective descent of local scheme models for an action quotient

This internal construction combines the canonical action quotient sheaf with
the published effective fppf descent theorem for separated locally quasi-finite
schemes. It assumes actual local scheme presentations and does not construct
them from reductivity.

A local comparison with the quotient sheaf times a represented parameter
respects that parameter. The proof cancels the locally surjective presentation
as an epimorphism in actual fppf sheaves. The comparison therefore gives a
pullback square over the relative base, using the universal property of the
product over a terminal presheaf.

For a free action, suppose every arrow of an fppf covering sieve of the relative
base has a flat, surjective, locally finitely presented scheme presentation
whose kernel on every relative test is equality of the parameter and an action
orbit. Suppose the local parameter scheme is separated, locally quasi-finite,
and locally of finite type over the cover. The common-kernel comparison and
the preceding pullback square provide the local models required by effective
descent. The resulting global scheme represents the canonical quotient sheaf.
Full faithfulness of the relative Yoneda functor constructs its actual class
morphism, compatibly with the canonical sheaf quotient map. The
`QuotientRepresentation` structure bundles this scheme, morphism, natural
isomorphism, and compatibility; `quotientRepresentationOfLocalPresentations`
constructs that bundle from the stated local presentations.
