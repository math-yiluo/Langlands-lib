# Finite Levi restriction from parabolic projection and tangent grading

Module `Langlands.Automorphic.GroupSchemeLeviCenterRestrictionReduction`, namespace
`Langlands.Automorphic.GroupSchemeFunctions`.

## The proposition

`ParabolicLeviCenterRestrictionReductionStatement.{u}` is the implication

```
ParabolicCenterProjectionFiniteStatement.{u, u} →
  ParabolicLeviTangentGradingStatement.{u} →
    ParabolicLeviCenterRestrictionStatement.{u}
```

between three propositions of the Library.

- `Langlands.Algebra.ParabolicCenterProjection.ParabolicCenterProjectionFiniteStatement`
  (module `Langlands.Algebra.ParabolicCenterProjectionFiniteStatement`) gives finiteness
  for an algebra map of enveloping centres that is congruent to the identity modulo the
  right ideal of the positive eigenvectors. It assumes a reductive finite-dimensional
  complex Lie algebra, an integral grading element `H` and an injective Lie map onto
  its centralizer.
- `ParabolicLeviTangentGradingStatement` (module
  `Langlands.Automorphic.GroupSchemeParabolicTangentStatement`) gives reductivity of the
  complexified tangent Lie algebra of the infinite adelic points of a connected reductive
  group. For a rational parabolic it supplies an integral grading element whose centralizer
  is identified with the complexified Levi tangent algebra by the Levi derivative, and whose
  positive part is the range of the complexified radical derivative.
- `ParabolicLeviCenterRestrictionStatement` (module
  `Langlands.Automorphic.GroupSchemeLeviCenterRestriction`) asserts that for every archimedean
  translate `a`, a finite algebra map of the actual enveloping centres intertwines the
  translated Levi restriction of plot-smooth functions invariant on the left by the
  radical.

`parabolicLeviCenterRestrictionReduction` proves the implication; it is
`parabolicLeviCenterRestriction_of_tangent`.

## The proof

Write `φ` and `ψ` for the point maps of `l ≫ q` and `iV ≫ q` on infinite adelic points.

1. **Normality.** `exists_radical_conj`: for Levi points `m` and radical points `v` there is
   `v'` with `φ(m) ψ(v) = ψ(v') φ(m)`. This is normality of the range of `iV` in `Q`
   (`IsUnipotentRadical.isNormal`), applied to the points over the infinite adele ring and
   pushed forward by the homomorphism of points of `q`.
2. **Radical derivatives vanish along the Levi.** `IsRadicalLeftInvariant q iV u` says
   `u(ψ(v) x) = u(x)`. `pointPullback_differential_radical`: for such `u` and a tangent
   vector `Y` of the radical points, the derivative of `u` in the direction `dψ Y`
   restricts to zero on the Levi. At `φ(m)` the left-translation identity
   `groupDirectionalValue_leftTranslation` and the chain rule
   `groupDirectionalValue_comp_hom` (module `Langlands.Geometry.Manifold.SmoothGroupHomLie`)
   reduce it to the derivative at `1` of
   `v ↦ u(φ(m) ψ(v))`, which is constant by step 1.
3. **Invariance is preserved.** `IsRadicalLeftInvariant.envelopingAction`: by
   `plotSmoothEnvelopingAction_leftTranslation` (module
   `Langlands.Automorphic.GroupSchemeAutomorphicLeftTranslation`), every enveloping operator
   preserves radical left invariance.
4. **The positive ideal acts by zero along the Levi.** `pointPullback_positiveRightIdeal`:
   given that the range of the complexified radical derivative is the span of the positive
   eigenvectors of `H`, every element of `positiveRightIdeal H` acts on a radical-invariant
   function by an operator whose Levi pullback vanishes. On a generator `ι(Y) w`, the
   function `w · u` is radical-invariant by step 3, `Y` is a complexified radical
   derivative, and step 2 applies on pure tensors.
5. **The identity translate.** `exists_leviCenterProjection` applies the tangent grading
   statement to the given data, including an atlas of `V`.
   The complexified Lie differential `j = complexPointLieDifferential` of `φ` (module
   `Langlands.Automorphic.GroupSchemePointDifferential`) satisfies the hypotheses of
   `Langlands.Algebra.ParabolicCenterProjection.exists_centerProjection`, which gives `p`
   with `z - U(j)(p z) ∈ positiveRightIdeal H`; the finiteness statement makes `p` finite.
   For radical-invariant `u`, `pointPullback_envelopingAction` turns the pullback of
   `U(j)(p z) · u` into `p z` acting on the pullback, and step 4 kills the remainder.
6. **A general translate.** `parabolicLeviCenterRestriction_of_tangent` deduces the
   affineness of `V` from the closed immersion `iV ≫ q` into the affine `G` and obtains
   its atlas using `Langlands.AlgebraicGeometry.smoothConnectedRelativeDimension`.
   It applies step 5 and precomposes `p` with `centerConjugationAlgHom hG a`, the
   adjoint action of `a` on the centre (surjective by
   `centerConjugationAlgHom_surjective`, hence finite). The translated
   restriction `infiniteLeviRestriction l a` is the pullback of the right translate
   `R(a)`, `R(a)` preserves radical invariance, and
   `adelicPlotSmoothEnvelopingRightCovariance` (module
   `Langlands.Automorphic.GroupSchemePlotSmoothRightCovariance`) gives
   `R(a)(z u) = Ad(a)(z) (R(a) u)`.

## Provenance

The differential-operator transfer is the one used in Mœglin–Waldspurger,
*Spectral Decomposition and Eisenstein Series* (1995), I.2.17, printed pp. 37–38
(PDF pp. 20–21), registered as `moeglin-waldspurger-1995-growth-and-constant-terms`.
Harish-Chandra, *Automorphic Forms on Semisimple Lie Groups* (LNM 62, 1968),
Chapter I, §6, printed p. 19 (PDF p. 29), gives the half-trace shift of the finite
centre homomorphism and its congruence modulo the left ideal \(U(\mathfrak g)\mathfrak n\).
The source is registered as
`provided-d0ff4732ff6b5d8ecf8562752577df639622e8aad2899ef307bc320213b534af`.
The raw projection used here corresponds to absorbing that shift into the projection
and transporting the congruence by the principal antiautomorphisms, as described in
`Langlands.Algebra.ParabolicCenterProjectionFiniteStatement`. The resulting right
ideal \(\mathfrak n U(\mathfrak g)\) has the radical derivative as the leftmost
factor, which gives the vanishing in step 4. Precomposition by the adjoint action
then gives the operator transfer at a general translate.
