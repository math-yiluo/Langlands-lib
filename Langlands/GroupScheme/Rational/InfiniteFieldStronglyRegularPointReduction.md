# Strongly regular rational points from the algebraically closed case

Author: Worker 1531.

This module proves one conditional result. The algebraically closed statement
`AlgClosedStronglyRegularTorusPointStatement` (module
`Absolute/StronglyRegularTorusPointStatement`) implies the published
`InfiniteFieldStronglyRegularPointStatement` (module
`Rational/InfiniteFieldStronglyRegularPointStatement`). Everything else it uses
is already proved in the Library. It does not prove the algebraically closed
statement.

## Declarations

- `InfiniteFieldStronglyRegularPointReductionStatement : Prop`, at universe
  `u`, is the implication
  `AlgClosedStronglyRegularTorusPointStatement.{u} →
  InfiniteFieldStronglyRegularPointStatement.{u}`.
- `infiniteFieldStronglyRegularPointReduction :
  InfiniteFieldStronglyRegularPointReductionStatement.{u}` proves it.

Once the algebraically closed statement is proved, the target follows by
applying this theorem to that proof.

## Proof

Let `K` be an infinite field and `H` a connected reductive group over `K`.
Write `K̄ = AlgebraicClosure K` and `b = toAlgebraicClosure K`, the morphism
`Spec K̄ ⟶ Spec K`.

1. Maximal torus. `maximalTorusExistence` gives a commutative `T` and
   `j : T ⟶ H` with `IsMaximalTorus j`. By the forward direction of
   `maximalTorusBaseChange` (Milne 17.82), the base change `j_K̄ : T_K̄ ⟶ H_K̄`
   is a maximal torus. `IsConnectedReductive.baseChange_toAlgebraicClosure`
   shows that `H_K̄` is connected reductive.
2. Strongly regular open set. The hypothesis, applied to `K̄`, `H_K̄` and `j_K̄`,
   gives a nonempty open `U` of `T_K̄` such that every `K̄`-point of `T_K̄` in
   `U` has all-test centralizer inside `T_K̄`.
3. A rational point in `U`. `T` is a `K`-torus, so its rational points are
   dense (`IsTorus.hasDenseRationalPoints_of_finiteGaloisSplitting` with
   `torusFiniteGaloisSplitting`). By
   `hasDenseGeometricRationalPoints_of_hasDenseRationalPoints`, the scalar
   extensions `geometricRationalPoint p` of the `K`-points `p` of `T` are
   dense in `T_K̄`. So some `p` has extension `t` meeting `U`. Since `Spec K̄`
   has a single point, the image of `t` lies in `U`.
4. The witnesses are `x = p ≫ j`, the torus `T` and `j`. `IsTorus` and
   `IsClosedSubgroup` are the first two parts of `IsMaximalTorus j`.
5. Descent. Let `Z` be a test over `K` and `c : Z ⟶ H` a point commuting with
   `toUnit Z ≫ x`. Put `V = Z_K̄`, let `q : V ⟶ Z` be the first projection
   (`EnvelopeBaseChange.pullbackFst`) and `c' = c_K̄ : V ⟶ H_K̄`.
   - Under `baseChangePointsEquiv b H V`, `c'` goes to `q ≫ c`
     (`EnvelopeBaseChange.baseChangePointsEquiv_pullback_map`). The point
     `toUnit V ≫ t ≫ j_K̄` goes to `q ≫ toUnit Z ≫ x`, by
     `baseChangePointsEquiv_naturality`, `geometricRationalPoint_natural`,
     `MatrixRepresentation.baseChangePointsEquiv_geometricRationalPoint` and
     uniqueness of maps to the terminal object.
   - The equivalence is multiplicative and injective, and `q ≫ -` preserves
     products. So `c'` commutes with `toUnit V ≫ t ≫ j_K̄`, and step 2 gives
     `s` with `s ≫ j_K̄ = c'`.
   - `SubgroupFunctor.range_baseChangeHom` and
     `SubgroupFunctor.mem_baseChange` turn this into: `q ≫ c` factors through
     `j`. The map `q.left` is a base change of the faithfully flat,
     quasi-compact `b` (`fieldExtension_fpqc`), hence an effective
     epimorphism. `j` is a monomorphism (`IsClosedSubgroup.mono`). So
     `SubgroupFunctor.mem_range_of_comp_mem_range` shows that `c` itself
     factors through `j`.

## Literature

Steinberg (1965), §10 (printed p.78, PDF p.31), finds a strongly regular
rational element by 2.15 and density of rational points in the whole group.
This proof instead works inside a maximal `K`-torus `T`. It uses the open set
of strongly regular points of `T_K̄`, as in the proof of 2.15 (printed p.54,
PDF p.7), and density of rational points only for the torus `T`. So no
density theorem for reductive groups is needed. The descent of the
factorization along `K̄ / K` is the standard faithfully flat descent of
morphisms into a closed subscheme.
