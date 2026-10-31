# Actual coordinate scalar operators under changes of variables

This file builds on the data structure
`Langlands.Analysis.CoordinateScalarOperator E d r` of
`Langlands.Analysis.CoordinateScalarDifferentialOperator`: a real basis
`basis : Module.Basis (Fin d) ℝ E` of actual vectors of `E` and complex
coefficients `coefficient k w : E → ℂ` for every order `k : Fin (r + 1)` and
every ordered word `w : Fin k → Fin d`. That file is imported unchanged.

## Transport through a continuous linear equivalence

Let `E : Type v` and `G : Type w` be real normed spaces (any universes), let
`d r : ℕ`, `D : CoordinateScalarOperator E d r` and `e : E ≃L[ℝ] G`.
`CoordinateScalarOperator.transport D e : CoordinateScalarOperator G d r` keeps
`d` and `r` and is defined by:

- its basis is `D.basis.map e.toLinearEquiv`, so its `i`-th vector is
  `e (D.basis i)` (lemma `transport_basis`);
- its coefficient at order `k`, word `w` and point `y : G` is
  `D.coefficient k w (e.symm y)` (lemma `transport_coefficient`).

The coefficient equation holds for every order, including order zero and the
highest order `r`, and for every ordered word. So every lower-order coefficient
is carried along, and the values stay complex. Both lemmas hold by definition
(`rfl`) and are `@[simp]`. Nothing else is added. In particular, no
regularity, ellipticity or solution hypothesis or certificate is introduced.

## Coordinates in Euclidean space

`D.euclideanCoordinates : E ≃L[ℝ] EuclideanSpace ℝ (Fin d)` is defined as
`D.basis.equivFunL.trans (EuclideanSpace.equiv (Fin d) ℝ).symm`.

- Mathlib's `Module.Basis.equivFunL` is the continuous real linear equivalence
  `E ≃L[ℝ] (Fin d → ℝ)` that sends a vector to its coordinates with respect to
  `D.basis`. It gets the finite dimensionality of `E` from the finite basis
  itself. So no separate `FiniteDimensional` instance and no other carrier is
  assumed.
- `EuclideanSpace.equiv (Fin d) ℝ : EuclideanSpace ℝ (Fin d) ≃L[ℝ] (Fin d → ℝ)`
  is Mathlib's standard equivalence (`PiLp.continuousLinearEquiv`), which keeps
  every coordinate. Its inverse is used.

So `D.euclideanCoordinates x` is the coordinate vector of `x` with respect to
`D.basis`, viewed in Euclidean space. The norm and topology of `E` are not
changed. The target is a separate space with its usual Euclidean norm, and the
map is continuous in both directions for these two norms. No comparison
constants between the two norms are stated here.

`D.toEuclidean : CoordinateScalarOperator (EuclideanSpace ℝ (Fin d)) d r` is
`D.transport D.euclideanCoordinates`. Unfolding the definitions, its `i`-th
basis vector is `D.euclideanCoordinates (D.basis i)`, and its coefficient at
order `k`, word `w` and point `y` is
`D.coefficient k w (D.euclideanCoordinates.symm y)`. The file does not prove
that `D.euclideanCoordinates (D.basis i)` is the `i`-th standard unit vector.

## Degenerate cases

No hypothesis is added beyond those of the data structure. Dimension `d = 0`
is allowed (then `E` is the zero space and the target is
`EuclideanSpace ℝ (Fin 0)`), and so is order `r = 0`.

## Provenance and scope

This is an internal linear change of coordinates for the published
ordered-word coefficient data. It makes no claim from the literature. It is
meant to let a separately proved regularity theorem for operators on standard
Euclidean space apply to operators on their original finite dimensional
normed spaces. The following are separate obligations and are not proved here:
the identity relating the actions of `D` and `D.transport e`, the comparison of
principal symbols, the transport of coefficient analyticity and of
(uniform) ellipticity, the canonical-basis identity above, and the resulting
regularity implication.

Worker 116 wrote the Lean definitions and lemmas and the first version of this
explanation. Worker 1085 checked them and revised this explanation.
