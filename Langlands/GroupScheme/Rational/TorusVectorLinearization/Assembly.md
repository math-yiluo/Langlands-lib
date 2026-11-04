# Torus linearization from the linearization of abstract point actions

This module reduces `TorusVectorActionLinearizationStatement` to a statement about
the abstract structure `TorusLinearization.PointAction` in prime characteristic.

## Scalar linearity from the matrix form

`TorusLinearization.PointAction.act_smul_of_pull_eq_sum` (namespace
`Langlands.GroupScheme.TorusLinearization`). Let `a : PointAction k K I n`, and let
`Φ Q : Fin n → MvPolynomial (Fin n) k` satisfy `aeval Q (Φ i) = X i` for all `i`.
Let `B` be a `k`-algebra and `t : a.Pt B` a point. Suppose a matrix
`b : Fin n → Fin n → B` satisfies

`a.pull t (Φ i) = ∑ j, b i j • map (algebraMap k B) (Φ j)` for all `i`.

Then for every scalar `c : B` and vector `y : Fin n → B`,

`(fun i => aeval (a.act t (fun j => aeval (c • y) (Q j))) (Φ i)) =
  c • fun i => aeval (a.act t (fun j => aeval y (Q j))) (Φ i)`.

In words: in the coordinates `Φ`, the action of `t` commutes with scalars.

Proof. Fix `w : Fin n → B` and `i`. Write `Q(w)` for the vector
`fun j => aeval w (Q j)`. By `PointAction.aeval_pull`, the `i`-th coordinate
`aeval (a.act t (Q(w))) (Φ i)` equals `aeval (Q(w)) (a.pull t (Φ i))`. By the
matrix form, this is `∑ j, b i j * aeval (Q(w)) (Φ j)`. Substitution composes
(`comp_aeval_apply`), so `aeval (Q(w)) (Φ j) = aeval w (aeval Q (Φ j)) = w j`.
Hence the `i`-th coordinate is `∑ j, b i j * w j`, which is linear in `w`. The
claim is the case `w = c • y` compared with `w = y`.

## The reduction

`torusVectorActionLinearization_of_linearizing` (namespace
`Langlands.GroupScheme.RelativeRoot`) assumes `hcore`. Let `k` be a field of
prime characteristic `p`, let `K` be a field extension of `k`, and let `I` be
finite. For every abstract point action `a : PointAction k K I n`, `hcore`
provides tuples `Φ Q : Fin n → MvPolynomial (Fin n) k` such that:

- each `Φ i` is additive (`IsAddPoly`);
- `Φ` and `Q` are mutually inverse under substitution: `aeval Φ (Q j) = X j`
  and `aeval Q (Φ i) = X i`;
- for every `k`-algebra `B` and point `t : a.Pt B`, there is a matrix
  `b : Fin n → Fin n → B` with
  `a.pull t (Φ i) = ∑ j, b i j • map (algebraMap k B) (Φ j)` for all `i`.

This is the shape of the conclusion of the abstract linearization theorem for
point actions. From `hcore` the theorem concludes
`TorusVectorActionLinearizationStatement`.

## Proof

`torusVectorActionLinearization_of_charP` reduces the target to prime
characteristic `p`, with natural coordinates scalar linear on coefficient tests.
In characteristic zero it uses the published scalar-linearity theorem. In both
characteristics, affineness of the torus upgrades linearity on coefficient tests
to linearity on all scheme tests. Then take a torus `T` and an action `a` of `T` on
a vector group `V`:

1. `IsVectorGroupOfDimension V n` supplies natural coordinates `e`.
2. `IsTorus T` supplies a field extension `K` of `k` and a splitting
   `s : T_K ≅ splitTorus (Spec K) I` with `I` finite.
3. `hcore` applied to `torusPointAction s a he` yields `Φ`, `Q` and, for each
   point, a matrix `b`. The point action's `act` is the coordinate action
   `coordinateAction a e`, by definition.
4. `act_smul_of_pull_eq_sum` turns the matrix form into scalar linearity of the
   coordinate action read in the coordinates `Φ`.
5. `exists_isAffineLinear_of_polynomials` turns `Φ`, `Q` into natural coordinates
   on which the action is scalar linear on coefficient tests.

## Provenance

This reduction is internal to the proof of
`TorusVectorActionLinearizationStatement`. It does not formalize a statement from
the literature, and its route is the project's own derivation. The published
statement's Markdown cites two separate passages of Conrad–Gabber–Prasad,
*Pseudo-reductive Groups*, 2nd ed. (2015), one for each characteristic:

- Characteristic zero: the discussion following Definition A.1.1, printed p.466
  (PDF p.492). Over a field of characteristic `0` a vector group has a unique linear
  structure and all homomorphisms are linear. The formal proof uses the published
  theorem `isLinearVectorCoordinates_of_charZero` for this case.
- Positive characteristic: Theorem B.4.3, printed p.577 (PDF p.603). It treats a
  smooth `p`-torsion commutative affine group with a torus action and has no
  characteristic-zero case. Its existence part comes from Propositions B.4.1 and
  B.4.2, printed pp.575–577 (PDF pp.601–603), through an equivariant embedding into
  a linear representation and an equivariant automorphism of that representation.

The case split (`torusVectorActionLinearization_of_charP`) combines these two
sources and is part of the formalization, not of B.4.3. In positive
characteristic, the formal proof does not follow the geometric argument of
B.4.1–B.4.2. It instead obtains new coordinates given by additive polynomials, in
which the torus acts linearly, from the abstract point-action theorem `hcore`.
