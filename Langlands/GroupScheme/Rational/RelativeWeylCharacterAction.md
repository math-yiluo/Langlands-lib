# The faithful relative Weyl action on all characters of a split torus

Author: Worker 37.

This is an internal derivation from the published definitions of split tori,
normalizing points, characters and the relative Weyl quotient. It does not
assume a relative root system. Its main action is on the entire character
lattice.

For any base scheme, characters separate homomorphisms into a split torus.
The proof transports a splitting isomorphism to commutative group schemes
and uses the identity decomposition as the sum of coordinate projections
followed by coordinate inclusions. Applying this separation to an
automorphism shows that trivial character action forces that automorphism
to be the identity. Thus the kernel of `weylAction i` is exactly the
centralizer points, for every split torus embedded by a monomorphism.

Over a field, `relativeWeylCharacterAction i` descends the full character
action to the existing quotient `relativeWeylGroup i = N(k)/Z(k)`.
The exact kernel calculation proves this action injective. These results
need neither reductivity nor maximality of the split subtorus.

These are supporting lemmas for the unrestricted relative-root-system
task. They do not establish its root-system existence, its Weyl-image
equality or root-span faithfulness for a connected reductive
group.
