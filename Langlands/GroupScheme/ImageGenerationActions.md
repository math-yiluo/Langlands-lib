# Scheme actions and equivariant ordered product maps

This internal interface supplies the action morphisms and intrinsic laws used
with the invariant subgroup-generation argument in Conrad–Gabber–Prasad,
*Pseudo-reductive Groups*, second edition (2015), paragraph preceding
Proposition 3.3.5, printed p.109 (PDF p.135), with the split-torus setting on
printed p.107; registered source `conrad-gabber-prasad-2015-pseudo-reductive`.
Stability of the closed envelope is an explicit premise here.

`PointwiseSchemeAction H V` is an actual morphism from `H.X ⊗ V` to `V` whose unit and
associativity laws hold on all test schemes. `V` is an arbitrary scheme over
the base and carries no required group structure. `act` is evaluation by
composition; its naturality follows from the binary product lifting laws.
`IsEquivariant` asserts all-test intertwining of actual morphisms and is
equivalent to a single equality of scheme morphisms, by evaluation at the
universal pair and precomposition.

The actual diagonal finite-power action is a product lift of the coordinate
actions. Its projection law, unit law and associativity law follow from the
source action and the product universal property. The existing
`AutomorphicAction` converts to this general scheme action by retaining its
action morphism and laws. An acting point preserves every ordered list product
because its action is a group automorphism.

Consequently, an equivariant source morphism has equivariant ordered product
maps on every finite power. The implemented proof evaluates coordinates and
uses preservation of the ordered list product, without commuting any factors.

For a conditional `GeneratedImage f` and stability of its fixed closed
envelope under the ambient automorphic action, `GeneratedImage.action` reuses
`AutomorphicAction.onRepresentedSubgroup`. Its inclusion intertwines the
actions. Cancellation of that inclusion proves equivariance of the actual
factor morphism; the finite-product theorem then proves equivariance of every
`powerMap`. These results require neither a torus nor geometric regularity.
Representability, stability and positive finite-product dominance are separate
geometric assertions.
