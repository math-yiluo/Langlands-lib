# Split-torus domination of full torus-quotient kernels

This internal construction combines the actual kernel difference morphism with
the full diagonalizable kernel model and finite-separable torus extraction. It
is a prerequisite for rational maximal-torus conjugacy, not a proof of that
conjugacy theorem.

For a split commutative torus T over any field k,
`Diagonalizable.splitTorusDiagonalizableIso` identifies T with D(X*(T)), using
evaluation of actual characters on every test scheme. The two point models are
natural under pullback, so `isoOfPointModels` gives an actual group-scheme
isomorphism. The character lattice is finitely generated: choose split
coordinates, identify their characters with a finite power of the integers, and
transport finite generation across the character-lattice isomorphism.

For a homomorphism f:T→Q of split tori,
`Diagonalizable.splitTorusKernelProductIso` constructs

    T × ker(f) ≅ D(X*(T) × coker(f*)).

It tensors the torus isomorphism with `homKernelDiagonalizableIso` and then uses
the inverse of `productIso`. The quotient character group is the full cokernel,
with all torsion retained; it is not saturated.

For a smooth affine group H, a torus quotient q:H→Q, and a pointed morphism
p:D→H from a split torus, pointed torus rigidity gives the homomorphism
f=q∘p. When Q is split, `TorusKernelDomination.diagonalizableParametrization`
composes the inverse of the displayed product isomorphism with the actual
kernel difference morphism (d,t)↦p(d)⁻¹p(dt). If p and q are dominant, this
morphism to the full scheme-theoretic kernel of q is dominant. Dominance follows
from the previously proved kernel difference theorem and invariance under the
source isomorphism.

`exists_finiteSeparable_kernel_hasPointedSplitTorusDomination` only requires Q
to be a torus: its splitness follows from the pointed dominant split-torus
parametrization of H and dominance of q. Assume also that the full kernel of q
is smooth and connected. Its inclusion into H is closed because Q is separated,
so the kernel is affine. The smooth-connected-affine geometry theorem gives
geometric integrality. The displayed source lattice is finitely generated,
and the dominant diagonalizable extraction theorem therefore supplies a finite
separable extension L/k and an actual pointed dominant morphism from a split
torus to ker(q)_L.

The field and all witness types remain in the same universe. All characteristics,
finite fields, imperfect fields, and the full kernel are retained. No unipotence
hypothesis is needed for this construction. This does not establish that a
unipotent target with this parametrization is split, does not descend splitness,
and does not construct the initial torus quotient or a conjugator.
