# The left-right action attached to two group-scheme homomorphisms

This is internal infrastructure derived from the published group-scheme,
scheme-action, and centrality definitions.

For arbitrary group schemes `H` and `G` over `S` and homomorphisms
`f g : H ⟶ G`, `leftRightHom f g` is the actual morphism
`H × G ⟶ G` whose action on every test scheme is
`(h, x) ↦ f(h) x g(h)⁻¹`. The evaluation formula is
`lift_leftRightHom`. `leftRightAction f g` equips this morphism with the
standard categorical scheme-action structure, using
`schemeActionOfPointLaws`. The action law uses the two homomorphism laws,
reversal of multiplication under inversion, and associativity in `G`.
No commutativity or centrality is required to construct the action.

`leftRightHom_eq_snd_iff` proves that the action is trivial exactly when
`f = g` and their common value is central on all test schemes. In the forward
direction, evaluate at the unit of `G` to get equality of the homomorphisms,
then rearrange the action identity to obtain commutation with every test
point. In the reverse direction, centrality allows commuting `f(h)` past
`x` and cancelling its inverse.

`baseChange_leftRightHom` identifies the action morphism after arbitrary
base change with the left-right morphism of the two base-changed
homomorphisms. Its expression includes the canonical monoidal comparison
between a product of pullbacks and the pullback of the product.

`eq_of_central_reduction_of_action_rigidity` is a conditional reduction.
For a morphism of bases `b`, assume that every action of `H` on the
underlying scheme of `G` which becomes trivial after `b` was already
trivial. If the reductions of `f` and `g` agree and their common reduction
is central, the reduced left-right action is trivial. The supplied
action-rigidity hypothesis makes the original action trivial, so `f = g`.
The module does not prove that action-rigidity hypothesis for any class of
base morphisms.
