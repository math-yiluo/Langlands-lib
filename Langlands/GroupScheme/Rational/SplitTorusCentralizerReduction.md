# Arbitrary split-torus centralizers and their cocenters

Author: Worker 1282.

This module extends the implemented proof of `genericCentralizer` from maximal
split tori to arbitrary split-torus homomorphisms, then gives conditional
reductions for centralizer reductivity and finite Galois splitting of every
supplied cocenter. Its provenance is the existing Lean proof in
`Rational/GenericCentralizerReduction`, whose argument uses only splitness of the
acting torus, together with the published dynamic and quotient interfaces.
No new numbered result is transcribed from literature.

`IsSplitTorus.dynamicCentralizer_eq_torusCentralizer` applies to every
homomorphism `i : T → G` from a split torus into a smooth connected affine group
over an arbitrary field. For every generic integral cocharacter `ν` of `T`, its
dynamic centralizer equals the centralizer of the whole image of `T`, as subgroup
functors on all test schemes. The homomorphism need not be an embedding, and the
torus need not be maximal.

The proof uses the existing four unconditional theorems `dynamicSmooth`,
`dynamicConnected`, `dynamicLie` and `lieSubgroupEquality`. A generic cocharacter
has the same zero adjoint weight space as the whole torus. For every other
cocharacter of `T`, the weight-space inclusion and the existing Lie-algebra
centralizer criterion imply inclusion of centralizers. The split-torus
decomposition of its identity into characters followed by cocharacters then
implies centralization of the full torus. The reverse inclusion holds directly
by restriction to `ν`.

`IsSplitTorus.exists_cocharacter_centralizer_eq` combines this result with the
already proved existence of a generic integral cocharacter.

`SplitTorusCentralizerReductiveStatement.{u}` is the proposition that every
representative of the centralizer of a split-torus homomorphism in a connected
reductive group is connected reductive. The theorem
`splitTorusCentralizerReductive_of_dynamic` proves it from the explicit premise
`DynamicCentralizerReductiveStatement.{u}`. It chooses the cocharacter above,
applies that premise to the canonical closed dynamic-centralizer representative,
then transports reductivity through the isomorphism of representatives.
Consequently no closedness hypothesis on the supplied representative is needed.

Finally, `splitTorusCentralizerCocenter_finiteGaloisSplitting_of_inputs` also
assumes `CocenterQuotientExistenceStatement.{u}`. For every actual derived
subgroup of the supplied centralizer, and every supplied commutative fppf
quotient by its range, it provides a finite Galois field extension `E : Type u`
over which that quotient is split. It uses
`suppliedCocenter_finiteGaloisSplitting_of_existence` after proving reductivity
of the centralizer.

Both structural statements remain premises. The module does not construct a
Galois-permuted character basis and does not prove that a cocenter is induced.
