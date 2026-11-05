# Original general-linear finite-smooth differential comparison

This internal construction compares actual tangent differentiation on the
existing finite-plot-smooth group-scheme functions with the original
general-linear finite-smooth enveloping action. Let `F : Type u` be any number
field and `n` any natural number, including zero, and put
`G = GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)`. Affineness is
provided by the original general-linear theorem.

The comparison uses the unchanged
`GroupSchemeFunctions.finitePlotSmoothGeneralLinearEquiv`. Its domain is the
original `FinitePlotSmoothRationalFunctions F G`, consisting of actual
continuous rational-left-invariant adelic functions with smooth infinite
slices and a common open finite stabilizer. Its codomain is the original
`Langlands.Automorphic.FiniteSmoothRationalFunctions F n`. Neither carrier is
replaced, and the ambient comparison already preserves the positive right
action `R(g)f(x) = f(x * g)`.

`finiteSmoothSlice_finitePlotSmoothGeneralLinearEquiv` proves that the slice
of the compared function at `finiteHomeomorph b` is the original
`GeneralLinearGroupPoints.plotSmoothGeneralLinearEquiv` applied to its actual
slice at `b`. Subtype extensionality reduces this to the existing equality
`infiniteSlice_continuousGeneralLinearEquiv`. Thus both the finite and infinite
factor maps are the original actual-point/matrix homeomorphisms.

For a supplied algebraic `SmoothOfRelativeDimension d G.X.hom`, select exactly
the completion structures `completionRCLike` and the original atlas
`InfiniteAdelicGroupPoints.smoothChartedSpace F G hsmooth`. Its real identity
tangent is `GroupLieAlgebra` with model `smoothModel F d`. The equivalence
`GeneralLinearGroupPoints.infiniteRealLieAlgebraEquiv` is the actual derivative
at the identity of the original infinite-point/mixed-matrix diffeomorphism.
No tangent identification is assumed as an extra premise.

`finitePlotSmoothGeneralLinearEquiv_differential` proves that applying the
actual finite-smooth derivative at `X` and then the original comparison gives
the original `finiteSmoothEnvelopingAction` at
`envelopingGenerator (complexify (infiniteRealLieAlgebraEquiv X))`, applied to
the compared original function. The proof tests all original finite-smooth
slices, whose extraction is faithful. Surjectivity of the original finite
homeomorphism reduces each test to the slice comparison above. The actual
slice-derivative formula and
`GeneralLinearGroupPoints.plotSmoothGeneralLinearEquiv_differential` turn
the left side into the original `ArchimedeanGL.smoothDifferential`. On the
right, the original enveloping slice formula and its real-generator identity
give that same operator. The positive right convention is retained, without
inversion or an extra sign.

`generalLinearRealFiniteSmoothDifferential` is the real-linear map into
complex-linear endomorphisms of the original general-linear finite-smooth
space obtained by conjugating the actual tangent action with the unchanged
finite-smooth equivalence. Its evaluation is exactly that conjugation.
`generalLinearRealFiniteSmoothDifferential_eq_generator` identifies each
endomorphism with the existing finite-smooth enveloping generator. This
follows from the preceding intertwining identity and the equivalence inverse
law.

`finitePlotSmoothGeneralLinearEquiv_reductiveDifferential` specializes the
same result to the dimension proved from the original connected-reductivity
theorem and exactly `reductiveChartedSpace`. Its tangent comparison is
`reductiveInfiniteRealLieAlgebraEquiv`. It has no separate dimension or
analytic-smoothness premise and imposes no positive-rank restriction.

The provenance is internal: the construction composes the original function
equivalences, the actual tangent differential and its already constructed
infinite general-linear comparison with the original `EnvelopingAction`
slice laws. The supporting slice reconstruction and descent arguments retain
Worker 72's contribution. The included manifold and differential supports
retain their actual contributing authors. No external assertion is newly
transcribed.

These results identify first-order real tangent operators under the original
comparison. They do not assert bracket compatibility for the general tangent
algebra or construct a general complexified Lie or enveloping action. The
exponential-curve comparison, derivative growth estimates, split-centre
descent, measures, reduction theory, finite volume, and cuspidal L2 realization
remain separate obligations.
