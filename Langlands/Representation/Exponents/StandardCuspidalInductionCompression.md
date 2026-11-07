# Native compression on actual standard cuspidal inductions

Worker 1751. This internal contribution connects the native whole-cuspidal
compression result to actual normalized induction from a literal standard Levi.
It derives its comparisons and stability assertions from the existing Library
constructions; it does not claim a separate original-source formalization.

`rationalInertiaInductionIsoOfEmbeddedLevi` compares actual induction functors
when their embedded parabolic, Levi and radical subgroups are equal and their
inverse Levi homeomorphisms give equal ambient points. After substituting the
three subgroup equalities, extensionality identifies the homeomorphisms. Proof
irrelevance identifies the semidirect-decomposition and radical-closedness
witnesses. The resulting induced objects, including their normalization, agree.

The three `standardCompression_*Points` theorems evaluate the published
all-test representation equalities for the canonical standard parabolic,
Levi and radical at the rational-point test scheme. For the two subgroup
images inside the parabolic, the canonical composition identities first
identify their ambient scheme maps. The theorem
`standardCompression_leviHomeomorph_coe` compares the represented and literal
canonical Levi homeomorphisms: both send each point by the same standard
Levi inclusion. Applying the preceding induction comparison gives
`standardCompression_inductionIso` on every rational-Levi representation.
This is an isomorphism of the actual induced smooth representations.

`standardCuspidalInduction_eventuallyStable_of_nativeJacquet` derives
maximality of the canonical intrinsic Levi torus from ambient maximality.
The published standard-family comparison supplies genericity of its
cocharacter. The theorem then applies
`rationalCuspidalInduction_eventuallyStable_of_nativeJacquet` to the
represented standard induction. Thus output dynamic Iwahori contraction
and commutation of the compressing element with every output-Levi point
enter the native generator theorem. The resulting positive stable power
passes through `standardCompression_inductionIso` by the published
compression retract theorem. Its exponent and positivity witness are
retained verbatim.

`literalLeviInduction_eventuallyStable_of_nativeJacquet` applies this result
to every intrinsically cuspidal rational-Levi input, then uses
`literalLeviInduction_eventuallyStable_of_rationalImages`. That adapter
transports every proper standard Jacquet test across the canonical Levi
homeomorphism, and maps the same-carrier pullback roundtrip through
normalized induction. It therefore proves eventual stability for the
actual normalized induction of each literal inside-Levi cuspidal input.
No finiteness, admissibility, generation or length condition is imposed
on this cuspidal input.

The field universe `u` and original carrier parameter `uV` are independent.
The rational and literal Levi representations and their induced objects
have carrier universe `max u uV`. Eventual stability means that some
positive power has stationary kernel and image. The transport preserves
that chosen positive power; the exponent can depend on the given input.

The supplied compatible root presentation uses the canonical standard
parabolic and Levi maps. Its split component is supplied, rather than
constructed here. Ambient and intrinsic Levi local compactness and
nonarchimedean group structures, the intrinsic simple-root `Fintype`,
finite type of the represented Levi, semidirect decompositions, radical
closedness, projection continuity, inducing quotient compactness and
geometric radical identification remain explicit. So do connected
reductivity, maximal splitness, genericity, `DynamicLieStatement` and
`StandardCocharacterStatement`.

The representation-theoretic inputs also remain explicit: the actual
whole-cuspidal inertia product decomposition, compact-level finiteness of
visible actual inertia classes, the exact norm-kernel small-progenerator
property for every irreducible cuspidal representative, and
`RationalCuspidalNativeJacquetInputs`. The last predicate retains
admissibility of those irreducible representatives and native normalized
output-Jacquet finiteness of their universal induced modules. These
premises are used by the published whole-cuspidal theorem, rather than
being replaced with a cuspidal-induction stability assumption.

This contribution supplies a supporting implication toward VI.9.1.
It does not choose a single exponent before every ambient smooth
representation. Those retained structural and representation-theoretic
inputs, the passage through finite embeddings and kernels, the countable
uniformity argument, and the exact unrestricted
`UniformCompressionStabilizationStatement` remain separate obligations.
