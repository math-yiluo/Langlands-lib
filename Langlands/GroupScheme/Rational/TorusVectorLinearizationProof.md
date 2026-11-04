# Proof of linearization of torus actions on vector groups

`Langlands.GroupScheme.RelativeRoot.torusVectorActionLinearization` proves the
published proposition `TorusVectorActionLinearizationStatement.{u}`. Let `k` be any
field in universe `u`, `T` a torus over `k` (split or not), `V` a vector group of
dimension `n` (possibly `n = 0`), and `a` an automorphic action of `T` on `V`. Then
there are natural coordinates `e` of dimension `n` on `V` with
`IsLinearVectorCoordinates a e`. The proof adds no hypotheses and does not use any
conjugacy statement.

## Proof

The theorem is one application of
`torusVectorActionLinearization_of_linearizing` (module
`TorusVectorLinearization/Assembly`). That theorem takes a hypothesis `hcore` about
abstract point actions `PointAction k K I n` in prime characteristic `p` with `I`
finite. `hcore` requires additive polynomials `Φ`, together with polynomials `Q`
that are mutually inverse to `Φ` under substitution. The pullback of each `Φ_i`
along every point must be a linear combination of the `Φ_j`. Given `p` and `a`,
`PointAction.exists_linearizing` (module `TorusLinearization/Linearizing`) provides
exactly this.

## The route

Scheme side (modules under `TorusVectorLinearization/`):

- `CharacteristicSplit` separates the cases. In characteristic zero it uses the
  published scalar-linearity theorem. In both cases, affineness of the torus
  upgrades linearity on coefficient tests to linearity on all scheme tests.
- `PointActionInstance`, `SplitPoints`, `CoordinateActionPolynomial` and
  `PolynomialTransition` turn the action read in the input coordinates into a
  `PointAction` over a splitting field `K` of `T`. They also prove that the
  coordinate action is given by additive polynomials. By
  `AdditivePolynomialSupport`, these are `p`-polynomials in characteristic `p`.
- `Recoordinatize` and `Assembly` turn the polynomials `Φ`, `Q` and the matrix form of
  the pullbacks into new natural coordinates. The action is linear in these.

Algebraic side in prime characteristic `p` (modules under `TorusLinearization/`):

1. `AdditivePolynomials`, `Euclid`: additive polynomials are spans of the
   `X_j^(p^r)`. Spaces of additive polynomials have Frobenius bases, found by the
   Euclidean algorithm in the twisted polynomial ring `k{F}`.
2. `PointAction`, `Grading`: the abstract point action, the pullback of polynomials,
   and over `K` the weight grading coming from the split torus action.
3. `Descent`, `Universal`: a `k`-linear form `θ : K → k` with `θ 1 = 1` lets
   membership in `k`-subspaces descend from `K`. Stability is tested on the
   universal point, and fixed polynomials are those of weight `0`.
4. `GradedProjection`, `Complement`: a projection over `K` that respects the
   grading, descended by `θ`. It gives a stable complement of the fixed and higher
   additive polynomials.
5. `Generation`: a stable subspace `W` of additive polynomials. Its linear-part map
   is injective, and its Frobenius span contains the variables. `W` is the
   complement plus the span of a Frobenius basis of the fixed part. The proof uses
   purity and a graded Nakayama argument.
6. `Coordinates`, `NoetherianInverse`: a basis of `W` gives the coordinates `Φ` and a
   one-sided inverse `Q`. The inverse is two-sided because a surjective endomorphism
   of a Noetherian ring is injective.
7. `Linearizing`: assembles 5 and 6 into `PointAction.exists_linearizing`.

## Provenance

The theorem is the published statement. Its Markdown cites two separate passages of
Conrad–Gabber–Prasad, *Pseudo-reductive Groups*, 2nd ed. (2015):

- characteristic zero: the discussion following Definition A.1.1, printed p.466
  (PDF p.492): the linear structure on a vector group is unique and all
  homomorphisms are linear;
- positive characteristic: Theorem B.4.3, printed p.577 (PDF p.603), for smooth
  `p`-torsion commutative groups with a torus action. Its existence part is
  obtained from Propositions B.4.1 and B.4.2, printed pp.575–577 (PDF pp.601–603).

B.4.3 itself has no characteristic-zero case. The case split in `CharacteristicSplit`
is this project's combined derivation: it uses the published characteristic-zero
theorem for one case and a positive-characteristic argument for the other. In
characteristic `p` the formal argument is the project's own alternative to
B.4.1–B.4.3, though it reaches the same kind of conclusion. It finds coordinates
given by additive polynomials (the `p`-polynomials of Definition B.1.2 and
Proposition B.1.3) in which the torus acts linearly. The intermediate steps are
not those of the source. They work with points over algebras rather than with
subgroups of a linear representation. They build a stable generating space of
additive polynomials by composition division, the character grading, descent
along a `k`-linear form `θ` in place of Galois descent, and a graded projection
for the complement. Purity and weight induction come next, then the Noetherian
inverse and the natural polynomial change of coordinates.
