# Local maps for actual changes of adelic level

This helper supports the changing-level topology proof.
It defines a local model-point map as three actual pullback point
equivalences and one actual coefficient extension. Its double projection
to the original model is that coefficient extension. Continuity follows
by composing coefficient continuity with the three base-change
homeomorphisms. Local finite type and an open coefficient inclusion give
openness by the same composition. These two topological lemmas take both
coefficient rings to be local topological rings with open units. Reduced
source coefficients, an injective coefficient map and a separated model
give injectivity by the published separated coefficient theorem.
Bijective coefficient maps give bijective local maps.

Both arithmetic index matches keep the underlying actual place fixed.
The full number-field match fixes every infinite place. For each target
index the module constructs a local ring homomorphism together with its
projection identity, open-embedding property and bijectivity when the
coefficient ring does not change. These are identities except where an
integer factor becomes a completed-field factor, where they are the
original subring inclusions. Rewriting the index inside this simultaneous
construction makes the dependent source types agree. The projection
identity connects the maps with the literal adelic level inclusion.
Only finitely many target indices can have changed rings, since they
belong to the finite set T. Every local factor is reduced, since each is
a field or a subring of one.

This is derived internal work supporting Conrad Theorem 3.6, printed
pp.6–8 of *Weil and Grothendieck approaches to adelic points* (2011).
The local coefficient maps respect the original source integer scalars,
by their projection identities and the naturality of the arithmetic
diagonals. The module uses those algebra maps to construct the actual
local point transitions through the two target base changes. A point of the twice-base-changed model is determined by its projection
to the original model. Applying this criterion, the original coordinate
projection laws and the literal ring-map square proves that both arithmetic
transitions agree with these local maps in the original coordinates.
The global arithmetic conclusion is proved in the companion
`AdelicLevelModelTransitionTopologyProof` module.
