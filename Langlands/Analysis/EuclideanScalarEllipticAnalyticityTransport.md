# Scalar elliptic analytic regularity through the actual finite basis

This module proves the published proposition
`Langlands.Analysis.EuclideanScalarEllipticAnalyticityTransportStatement E d r`
of `Langlands.Analysis.EuclideanScalarEllipticAnalyticityTransportStatement`,
for every real normed space `E : Type v` in an arbitrary universe and every
`d r : ℕ`, including `d = 0` and `r = 0`. That proposition is the implication

`CanonicalEuclideanScalarEllipticAnalyticityStatement d r →
  ScalarEllipticAnalyticityStatement E d r`.

So the module shows that analytic regularity for scalar elliptic operators
on standard Euclidean space, with the canonical basis, implies the unchanged
generic assertion on `E`. It does not prove the canonical regularity premise.

The proof uses the published operator data
`Langlands.Analysis.CoordinateScalarOperator` and the published constructions
`CoordinateScalarOperator.transport`, `euclideanCoordinates` and
`toEuclidean` of `Langlands.Analysis.CoordinateScalarTransport`, together with
their `@[simp]` lemmas `transport_basis` and `transport_coefficient`. The
target statement's module and every module it imports are used unchanged.

## Helper lemmas

All helper lemmas lie in the namespace
`Langlands.Analysis.CoordinateScalarOperator`. In them, `E : Type v` and
`G : Type w` are real normed spaces in arbitrary universes, `d r : ℕ` are
arbitrary, `D : CoordinateScalarOperator E d r` and `e : E ≃L[ℝ] G`.
No finite-dimensionality, completeness or smoothness hypothesis appears.

- `iteratedFDeriv_comp_equiv`: for every `F : E → ℂ`, `k : ℕ`, `y : G` and
  `vectors : Fin k → E`,
  `iteratedFDeriv ℝ k (F ∘ e.symm) y (fun j => e (vectors j)) =
  iteratedFDeriv ℝ k F (e.symm y) vectors`.
  The proof specializes Mathlib's
  `ContinuousLinearEquiv.iteratedFDerivWithin_comp_right`, applied to
  `e.symm` on the whole space `E` (unique differentiability by
  `uniqueDiffOn_univ`), evaluates both sides at the vectors
  `e (vectors j)`, and simplifies `e.symm (e v) = v` and
  `iteratedFDerivWithin_univ`. Since the Mathlib identity has no
  differentiability hypothesis, neither does this one.
- `transport_action`: for every `F : E → ℂ` and `y : G`,
  `(D.transport e).action (F ∘ e.symm) y = D.action F (e.symm y)`.
  This is the comparison of the full differential expressions, with every
  order `k : Fin (r + 1)` from `0` to `r` and every ordered word. It follows
  by unfolding `action` and rewriting each term with `transport_coefficient`,
  `transport_basis` and `iteratedFDeriv_comp_equiv`.
- `transport_principalSymbol`: for every `y : G` and `ξ : G →L[ℝ] ℝ`,
  `(D.transport e).principalSymbol y ξ =
  D.principalSymbol (e.symm y) (ξ.comp e.toContinuousLinearMap)`.
  So the transported symbol on `ξ` is the original symbol on the pulled-back
  covector `ξ ∘ e`. It follows by unfolding `principalSymbol` and the two
  transport lemmas.
- `transport_analyticCoefficients`: for `S : Set E`, if
  `D.AnalyticCoefficientsOn S`, then
  `(D.transport e).AnalyticCoefficientsOn (e.symm ⁻¹' S)`. Each transported
  coefficient is `D.coefficient k w ∘ e.symm`. It is analytic near each point
  of `e.symm ⁻¹' S` by `AnalyticOnNhd.comp`, since `e.symm` is analytic
  (`ContinuousLinearEquiv.analyticOnNhd`) and maps that set into `S`.
- `transport_isElliptic`: for `S : Set E`, if `D.IsEllipticOn S`, then
  `(D.transport e).IsEllipticOn (e.symm ⁻¹' S)`. Let `y` be in the set and
  `ξ ≠ 0`. By `transport_principalSymbol`, it suffices that the pulled-back
  covector `ξ.comp e.toContinuousLinearMap` is nonzero. If it were zero, then
  evaluating it at `e.symm z` would give `ξ z = 0` for every `z : G`, so
  `ξ = 0`.
- `euclideanCoordinates_basis`: for every `i : Fin d`,
  `D.euclideanCoordinates (D.basis i) =
  (EuclideanSpace.basisFun (Fin d) ℝ).toBasis i`.
  The coordinates of the basis vector `D.basis i` in that basis are
  `Finsupp.single i 1`, so each coordinate `j` of both sides is `1` if
  `i = j` and `0` otherwise. The proof is extensionality in `j` and `simp`.
- `toEuclidean_basis`:
  `D.toEuclidean.basis = (EuclideanSpace.basisFun (Fin d) ℝ).toBasis`.
  The two bases agree on every index by `euclideanCoordinates_basis`, since
  the `i`-th vector of `D.toEuclidean` is
  `D.euclideanCoordinates (D.basis i)`.

## The main theorem

`Langlands.Analysis.euclideanScalarEllipticAnalyticityTransport`, for
`(E : Type v) [NormedAddCommGroup E] [NormedSpace ℝ E] (d r : ℕ)`, has type
`EuclideanScalarEllipticAnalyticityTransportStatement E d r`. A closing
`example` restates this type with all binders and is checked against the
theorem.

The proof assumes the canonical Euclidean assertion and takes an operator
`D : CoordinateScalarOperator E d r`, a set `S`, a function `F : E → ℂ` and
the five hypotheses of `ScalarEllipticAnalyticityStatement E d r`. Write
`e := D.euclideanCoordinates : E ≃L[ℝ] EuclideanSpace ℝ (Fin d)` and
`T := e.symm ⁻¹' S`. As a set, `T` is the image of `S` under `e`; the
proof works with the preimage form directly. Then:

1. `T` is open, as the preimage of the open set `S` under the continuous
   map `e.symm`.
2. `F ∘ e.symm` is smooth (`ContDiffOn ℝ ∞`) on `T`, by composing the
   smoothness of `F` on `S` with the smooth map `e.symm`.
3. `D.toEuclidean.action (F ∘ e.symm) y = 0` for every `y ∈ T`. Since
   `D.toEuclidean` is `D.transport e`, `transport_action` turns the left
   side into `D.action F (e.symm y)`, which vanishes because `e.symm y ∈ S`.
4. The canonical assertion applies to `D.toEuclidean`, `T` and
   `F ∘ e.symm`. Its basis premise is `toEuclidean_basis`. Coefficient
   analyticity and ellipticity on `T` are `transport_analyticCoefficients`
   and `transport_isElliptic`. It gives `AnalyticOnNhd ℝ (F ∘ e.symm) T`.
5. For `x ∈ S`, the point `e x` lies in `T`, so `F ∘ e.symm` is analytic at
   `e x`. Composing with the analytic map `e`
   (`ContinuousLinearEquiv.analyticAt`) and simplifying
   `e.symm (e x') = x'` gives `AnalyticAt ℝ F x`.

The conclusion `AnalyticOnNhd ℝ F S` is about the original space `E`, with
its original norm, topology and real scalar structure, and about the
operator's own basis. Every lower-order term enters through the full action
comparison. The coefficients and `F` stay complex valued and the domain stays
real. No hypothesis on `d` or `r` is added, so `d = 0` and `r = 0` are
covered.

## Provenance and scope

This is an internal proof: a linear change of coordinates and the chain rule
for iterated derivatives through a continuous linear equivalence. It
formalizes no literature theorem. It follows the route described in the
target statement's Markdown, with `e.symm ⁻¹' S` in place of `e '' S`.
The literature behind the regularity statements themselves is recorded in
the Markdown of `ScalarEllipticAnalyticityStatement` and
`EuclideanScalarEllipticAnalyticityTransportStatement`.

The module proves neither the canonical Euclidean regularity premise nor
`ScalarEllipticAnalyticityStatement` itself. It contains no weighted
estimate and no transport of uniform ellipticity, and it does not prove the
joint-finite analyticity theorem that this implication is meant to serve.

Worker 116 wrote the Lean proof and the first version of this explanation.
Worker 1085 checked the proof and rewrote this explanation.
