# A multiplicity-one detector identifies simple endpoints

Author: Worker 502.
`simpleEndpointMultiplicityOne` has exactly
`SimpleEndpointMultiplicityOneStatement` as its type and applies the complete
explicit-telescope core `simpleEndpointMultiplicityOneCore`, importing the
published target statement.

The criterion concerns an additive functor from smooth complex
representations of an arbitrary group with a topology to algebraic complex
representations of an arbitrary monoid. It preserves epimorphisms and
monomorphisms. The five group, monoid and carrier universes remain independent.
For an actual injection `j : P → A` with irreducible source and an actual
surjection `q : A → Q` with irreducible target, assume that one test object has
count one in `F A` and positive counts in `F P` and `F Q`. Each count includes
an actual finite simple-series witness. The conclusion is a categorical
isomorphism between the actual smooth objects `P` and `Q`.

The implementation splits on whether the composite intertwiner `q ∘ j`
vanishes. If it does not vanish, Mathlib's bijective-or-zero theorem for
intertwiners between irreducible representations gives a bijection.
`IntertwiningMap.ofBijective` and `SmoothRep.mkIso` supply the required
isomorphism.

In the zero case, functoriality and additivity make the image composite zero.
The published concrete descriptions of monomorphisms and epimorphisms
translate preservation into injectivity of `F j` and surjectivity of `F q`.
Form the actual kernel representation of `F q` and its inclusion. The
published `jordanHolderShortExactDecomposition` constructs finite simple-series
count witnesses for the kernel and `F Q`, whose counts sum to one. Restricting
the codomain of `F j` to the kernel gives an actual injective intertwiner.
The published `jordanHolderInjectiveMonotonicity` bounds the positive count of
`F P` by the kernel count. Multiplicity independence identifies the
decomposition's count for `F Q` with the supplied positive count. These two
positive natural numbers cannot sum to one, eliminating the zero case.

This is an internal derivation from actual kernel constructions, Schur's
bijective-or-zero argument, and the published finite-series multiplicity
theorems. It uses no source finite length, constituent uniqueness, full
exactness of the functor, or irreducibility assumption on the test object.
It imports no segment, multisegment, tempered or analytic classification
result. It does not construct the functor or establish the three count
hypotheses for any induction.
