# Right-translation covariance of actual real differentiation

This statement group specifies the elementary chain-rule compatibility of the
published right translations and real directional derivatives. All three
declarations are Prop-valued definitions in `Langlands.Automorphic`; this module
does not prove them.

For any number field `K : Type u` and any `n : ℕ`,
`SmoothRealDifferentialCovarianceStatement K n` quantifies over every
`g : InfiniteAdelicGL K n`, `X : ArchimedeanGL.RealLieAlgebra K n`, and
`f : ArchimedeanGL.SmoothFunctions K n`. It states

`R(g) (D(X) f) = D(Ad(g) X) (R(g) f)`,

where `R(g)` is exactly `ArchimedeanGL.smoothRightAction K n g` and `D(X)`
is exactly `ArchimedeanGL.smoothDifferential K n X`. The function space is
the published space of complex-valued, real-smooth functions on the actual
completion-based infinite group.

`FiniteSmoothRealDifferentialCovarianceStatement K n` quantifies over the same
`g` and `X`, and every `f : FiniteSmoothRationalFunctions K n`. It states the
same identity with

- `R(g) = finiteSmoothRightAction K n (AdelicGL.ofInfinite K n g)`;
- `D(X) = finiteSmoothEnvelopingAction K n
  (ArchimedeanGL.envelopingGenerator K n (ArchimedeanGL.complexify K n X))`.

Here the functions are actual continuous, rational-left-invariant adelic
functions with real-smooth infinite slices and a common open finite
stabilizer. The statement adds no automorphy, compact-finiteness,
center-finiteness, growth, or compact finite-level assumption.

In both statements, `Ad(g) X` is written directly as

```lean
(ArchimedeanGL.realLieAlgebraToMatrix K n).symm
  ((archimedeanGLCoordinates K n g : ArchimedeanMatrix K n) *
    ArchimedeanGL.realLieAlgebraToMatrix K n X *
    (archimedeanGLCoordinates K n g⁻¹ : ArchimedeanMatrix K n))
```

The equivalence `realLieAlgebraToMatrix` identifies the concrete real Lie
algebra with its underlying matrix space. The multiplicative coordinate
equivalence `archimedeanGLCoordinates` transports the completion-based
group to invertible matrices over the mixed real and complex archimedean
space. Thus the last factor is the inverse coordinate matrix, and the
expression is the direction `g X g⁻¹` transported back to the real Lie algebra.
No additional adjoint or enveloping automorphism is introduced.

The covariance orientation is determined by the published conventions:
`R(g)f(x) = f(x*g)` and `D(X)` differentiates at `x` in the matrix direction
`x*X`. The left side differentiates `f` at `x*g` in direction `(x*g)*X`.
For the right side, the chain rule for the map `x ↦ x*g` sends the direction
`x*(g*X*g⁻¹)` to `(x*g)*X`. This explains why conjugation is by `g` on the
left and `g⁻¹` on the right.

`RealDifferentialCovarianceStatement K n` is exactly the conjunction of
`SmoothRealDifferentialCovarianceStatement K n` followed by
`FiniteSmoothRealDifferentialCovarianceStatement K n`. It is the single
target for a subsequent proof of the smooth chain-rule identity and its
descent through the faithful `finiteSmoothSlice` maps.
The published `finiteSmoothSlice_envelopingAction` and
`ArchimedeanGL.envelopingAction_real_generator` identify each slice of the
adelic real-generator operator with the smooth directional operator.

The universe `u` is arbitrary. Each statement includes every infinite group
element, not merely elements of a chosen compact subgroup, and every natural
rank, including zero under the existing empty-matrix conventions.

The provenance is internal and derived from the actual definitions imported
through `Langlands.Automorphic.EnvelopingAction`, including
`Automorphic.Smooth`, `Global.ArchimedeanGL`,
`Global.ArchimedeanSmoothDifferential`, `Global.ArchimedeanLieAlgebra`, and
`Global.ArchimedeanEnvelopingAction`. The chain-rule explanation is mathematical
motivation for the statements, not a claim of an implemented proof.
Borel and Jacquet, *Automorphic forms and automorphic representations* (1979),
§2.2, printed p. 193 / one-based PDF p. 188, supplies the intended application
to right translation and differential actions on automorphic forms. These
covariance statements are not quotations of that section and do not assert
its admissibility or differential-growth conclusions.

Registered application source: `borel-jacquet-1979-automorphic`, retained in
`/home/taskhub/central-library/Borel-Casselman--Automorphic Forms, Representations and L-Functions (Corvallis)--1979/Part I.pdf`.
SHA256: `3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`.
