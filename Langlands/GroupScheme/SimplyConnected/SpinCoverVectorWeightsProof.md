# Vector weights of an aligned type-D spin cover

`Langlands.GroupScheme.spinCoverVectorWeights` has exactly the type
`SpinCoverVectorWeightsStatement.{u}`, with arbitrary universe parameter `u`.
It applies `spinCoverVectorWeights_of_representation_inputs` to the two
representation theorems `Quaternionic.orthogonalMoritaRepresentation` and
`OrthogonalMatrix.numberedCoverVector`.

The first input constructs the actual orthogonal Morita comparison,
including its fixed row equivalence and the scalar extensions of that
equivalence intertwining the inverse-right actions over every compatible
commutative coefficient algebra. The second input constructs numbered
characters of the supplied split pinning torus and a single vector
eigenbasis valid over every coefficient algebra, using the supplied
central cover and its full scheme-kernel alignment.

The applied reduction chooses the Morita comparison over
`AlgebraicClosure (SeparableClosure K)`, transports the given spin cover,
numbering and alignment, and descends the resulting characters to the
pinning torus over `SeparableClosure K`. Its multiplicity calculation uses
the actual cocharacter of the original maximal split torus, counts
homogeneous basis vectors by Laurent coefficient projectors, and cancels
the positive division degree. Thus the conclusion concerns the original
division-algebra weight spaces and retains the specified simple-root
equations and all signed-pair root equations.

No representation input remains as a premise of this theorem. It retains
the unchanged statement's hypotheses for arbitrary fields in every
characteristic, including finite fields and characteristic two, every
`n ≥ 4`, the actual Tits index, numbering, spin cover and alignment.

This is an internal composition of the named representation theorems
with the named reduction. It introduces no new literature assertion.
