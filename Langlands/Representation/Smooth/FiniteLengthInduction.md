# Finite-length preservation from the irreducible case

Worker 117 proves
`Langlands.SmoothRep.FiniteLengthInductionStatement.{uR,uG,uV,uS,uH,uW}` as the
closed theorem `finiteLengthInduction`. The applied version is
`preservesFiniteLength_of_irreducibles`.

This internal reduction concerns actual smooth representation categories. The
source coefficient ring is a field; the target coefficient ring is any
commutative ring. The coefficient, group, and representation carrier universes
of the two categories are independent. No topological group assumption is
required beyond the topological spaces used in smoothness.

The result assumes preservation of actual short exact sequences whose three
source terms have finite group-algebra length, and finite group-algebra length
of the image of every irreducible source object. It concludes preservation of
finite group-algebra length.

The implemented proof inducts on Mathlib's `IsFiniteLength` for modules over the
source group algebra. It realizes the submodule and simple quotient as actual
smooth representations using smoothness transfer along the inclusion and
quotient intertwiners. Exactness of their images makes the middle image
Noetherian and Artinian, hence of finite length. For the zero case, applying
exactness to the two identity maps of a subsingleton object proves that its
image is subsingleton, using the functor identity law. Thus no separate
additivity or preservation-of-zero assumption is needed. Finally, the
representation-to-module equivalence transports the conclusion to the original
source object without changing its carrier universe.

This is an internal algebraic argument formalizing the induction-on-length
step. It does not establish the irreducible-input theorem, exactness of any
particular parabolic induction functor, or the closed general induction
finite-length target. The module-to-representation proof pattern also appears
in `Langlands.Representation.Smooth.Admissibility.FiniteLengthProof`. This
module reuses `Langlands.representationToModuleIntertwiner` from the generic
`Admissibility.FiniteLengthReduction` module and
`hasFiniteLength_of_isIrreducible` from `IrreducibleRealization`. These general
interfaces introduce no dependency on the GL classification results imported
by the admissibility specialization.

The proof imports the published statement unchanged. Its prerequisites are
public Library results; this pair supplies the separate proof of the generic
reduction.
