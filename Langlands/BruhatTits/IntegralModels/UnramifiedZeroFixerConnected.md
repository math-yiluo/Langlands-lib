# Connectedness of maximal-unramified zero-fixer models

The proposition `UnramifiedZeroFixerConnectedStatement` says that the actual full
special fibre of every smooth integral model characterized by a zero fixer is
connected when the apartment set is nonempty and lies in one facet. It retains
arbitrary universe `u`, the original building and zero datum, and the supplied
model. No boundedness of the facet is assumed.

The theorem `unramifiedZeroFixerConnected` proves this proposition. The stronger
helper `unramifiedZeroFixer_hasConnectedFibres` proves connectedness of every
actual residue fibre of the supplied model.

The proof first treats a singleton. Construct the actual relative identity
component as an integral model of the same connected reductive generic group.
The whole-apartment zero fixer is the torus Iwahori image for an apartment
compatible maximal torus. The published connected-image theorem realizes this
Iwahori subgroup as the image of a smooth model with geometrically connected
fibres. Its composite generic map extends to the supplied model by the proved
strictly Henselian smooth-homomorphism extension criterion, since its integral
image fixes the whole apartment. Connected-source factorization places this
image in the neutral model.

Each root fixer is the image of the actual integral root model of the supplied
smooth zero-fixer model. These root models have geometrically connected fibres,
so their integral images also lie in the neutral model. The published
whole-apartment zero/sharp decomposition at a singleton therefore puts every
integral point of the full model in the neutral model. Extend the generic
identity in this direction. The neutral inclusion supplies the opposite
extension, and generic rigidity makes the extensions inverse isomorphisms.
Connected fibres of the neutral model transfer through this actual model
isomorphism.

Finally, the proved constancy of zero fixers on nonempty subsets of one facet
reduces any set in the proposition's domain to one of its points. The full
special fibre is the actual residue fibre at the closed point up to the
published homeomorphism, so connectedness of all fibres gives the conclusion.

This is an internal consequence of the imported Library theorems. It proves
only the connectedness input needed by the upstairs radical
factorization argument; it does not itself assert the radical-preimage
generation formula.
