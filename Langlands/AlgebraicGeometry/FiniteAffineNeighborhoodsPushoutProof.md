# Finite pinching preserves finite-set affine neighborhoods

`Langlands.AlgebraicGeometry.finiteAffineNeighborhoodsPushout` proves exactly
the published proposition `FiniteAffineNeighborhoodsPushoutStatement.{u}`.
It covers arbitrary schemes `X`, `Y`, `Z`, `P` in universe `u` and actual
morphisms `i : Z ⟶ X`, `j : Z ⟶ Y`, `a : X ⟶ P`, `b : Y ⟶ P`.
The hypotheses are that `i` is a closed immersion, `j` is finite, `X` and
`Y` satisfy `PointTopology.HasFiniteAffineNeighborhoods`, and
`IsPushout i j a b` holds in `Scheme`. The conclusion is that every finite set
of points of `P` lies in an affine open of `P`. The finite sets may contain
nonclosed points, and no other hypothesis is added.

## Implemented proof

The proof constructs one model pushout of the span and transfers the property
to the supplied pushout `P`. Its inputs are the following.

1. **Fibre hypothesis.** `FinitePinching.exists_affineOpen_fibre` (Library
   module `FiniteAffineNeighborhoodsPushoutCharts`) uses finiteness of `j` and
   the AF property of `X`. For each `y : Y`, the fibre `j ⁻¹' {y}` is finite,
   so its image under `i` lies in an affine open of `X`. This is the fibre
   hypothesis `hF` of the integral-pushout atlas. A finite morphism is
   integral, and Mathlib supplies that instance.

2. **Model pushout.** `IntegralSchemePushout.compatibleAffinePushoutAtlas i j hF`
   is the Library atlas from `IntegralSchemePushoutAtlas`. Its index type is
   `CompatibleAffinePairs i j`: every pair of affine opens `U ⊆ X`, `V ⊆ Y` with
   `i ⁻¹ᵁ U = j ⁻¹ᵁ V`. It attaches to each pair an affine model pushout of the
   restricted span. Call this atlas `D`. The Library construction
   (`IntegralSchemePushoutGlobal`) yields a scheme `D.scheme` with
   legs `D.left : X ⟶ D.scheme` and `D.right : Y ⟶ D.scheme`, and
   `D.isPushout_global : IsPushout i j D.left D.right`. The descent lemmas
   `D.left_isIntegral` and `D.right_isClosedImmersion`
   (`IntegralSchemePushoutDescent`) show that `D.left` is integral and `D.right`
   is a closed immersion. Their inputs are the atlas lemmas
   `compatibleAffinePushoutAtlas_inl_isIntegral` and
   `compatibleAffinePushoutAtlas_inr_isClosedImmersion`.

3. **Affine charts.** The new theorem
   `FinitePinching.hasAffineCharts_compatibleAffinePushoutAtlas` proves
   `FinitePinching.HasAffineCharts i j D.left D.right`. Given a compatible
   affine pair `(U, V)`, the pair itself is an index `t` of the atlas. The chart
   `D.chart t` is an open immersion from an affine scheme, so its range `W` is
   an affine open of `D.scheme` (Mathlib's `isAffineOpen_opensRange`). The
   Library equalities `D.chart_preimage_left t` and `D.chart_preimage_right t`
   state `D.left ⁻¹ᵁ W = U` and `D.right ⁻¹ᵁ W = V`. Only the resulting
   inclusions `U ≤ D.left ⁻¹ᵁ W` and `V ≤ D.right ⁻¹ᵁ W` are used.

4. **Compatible affine pairs around finite sets.**
   `exists_compatible_affineOpens_of_finite` is contributed by Worker 1770 in
   the module `FiniteAffineNeighborhoodsPinchingAux` that accompanies this proof.
   It takes finite sets `E ⊆ X` disjoint from the range of `i` and `F ⊆ Y`.
   It produces affine opens `U ⊇ E` and `V ⊇ F` with `i ⁻¹ᵁ U = j ⁻¹ᵁ V`.
   This is exactly the predicate `FinitePinching.HasCompatibleAffinePairs i j`.
   The module implements Ferrand's avoidance Lemma 5.5 and the
   compatible-neighborhood step of Theorem 5.4(a); its own Markdown describes
   the proof.

5. **Assembly and transfer.** The published theorem
   `FinitePinching.hasFiniteAffineNeighborhoods_of_model` takes the model
   pushout `D.isPushout_global` with an integral first leg and a
   closed-immersion second leg, the compatible-pair property (step 4), the
   chart property (step 3) and the supplied square `IsPushout i j a b`. It
   concludes AF for `P`. It first shows AF for the model. The legs of the model
   are closed and quasi-compact, so every point of the model lies in the range of
   `D.left` or of `D.right`. A finite set of points is split into the points
   coming from `Y` and the remaining points, which come from `X` outside
   the range of `i`. Steps 4 and 3 then give one affine open containing the
   whole set. Finally the unique isomorphism between the model and `P` given by
   the two pushout universal properties transports AF to `P`.

## Provenance

This proof implements Ferrand, *Conducteur, descente et pincement*
(Bull. Soc. Math. France 131 (2003)), Theorem 5.4(a), printed pp. 570–572,
registered as `ferrand-conducteur-descente-pincement-2003`. That is the
derived consequence recorded in the unchanged statement's Markdown. Ferrand's
ringed-space pushout is replaced by the Library's scheme constructed from
the compatible affine atlas, and the transfer to an arbitrary scheme pushout
uses the categorical uniqueness of pushouts. The route is otherwise Ferrand's:
split a finite set between the two sides, choose compatible affine
neighborhoods by prime avoidance, and take their affine pinching as the
neighborhood.

The global atlas, affine models and descent lemmas were supplied by
Worker 1764. Worker 1603 supplied the compatible covers, and the affine
pushout universal property by Workers 1568 and 336 underlies the affine models.
Worker 1770 wrote `FiniteAffineNeighborhoodsPinchingAux`. Worker 1495 wrote
the pushout-side helper module and this assembly.

The theorem proves only the AF property of the supplied pushout. It does not
add a pushout-existence conclusion, a conductor construction, an
algebraic-space identification or any representability statement.
