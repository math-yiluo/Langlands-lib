# The two identity slices of an augmented tensor product

Worker 1228. This is an internal algebraic calculation for the proof of the
semigroup commutator weight bound. Its source is the tensor calculation in
Conrad–Gabber–Prasad, *Pseudo-reductive Groups*, second edition (2015),
Lemma 3.3.4, printed pp.108–109 (PDF pp.134–135), registered as
`conrad-gabber-prasad-2015-pseudo-reductive`. The implemented proof uses the
splitting of an augmentation by the scalar inclusion; it works over any
commutative base ring.

For augmented commutative algebras `A` and `B` over `k`,
`leftIdentitySlice` evaluates the first tensor factor by the augmentation
and `rightIdentitySlice` evaluates the second. They are the actual algebra
homomorphisms obtained from tensor products of algebra maps and the unit
isomorphisms.

`augmentationPart` subtracts the scalar part of an element, and
`augmentationKernelProjection` gives this map with codomain the actual
linear kernel. Tensor induction shows that applying either scalar-subtraction
map to a tensor subtracts the corresponding slice, included back into the
tensor product. Thus, when both slices vanish, tensoring the two kernel
projections supplies a preimage under the tensor of the kernel inclusions.
The reverse inclusion follows by tensor induction, since either slice kills
a pure tensor of elements of the two augmentation kernels. This proves
`ker_leftIdentitySlice_inf_ker_rightIdentitySlice`.

`map_augmentationKernel_mem_tensor` applies that equality to an algebra
homomorphism whose restrictions to the two identity slices are constant at
the source augmentation. This is the algebraic form of the step used for a
commutator pullback in CGP: the commutator is the identity on both slices.
The module does not construct a commutator morphism, an action on coordinates,
or a scheme-theoretic image, and does not prove the full semigroup commutator
statement.
