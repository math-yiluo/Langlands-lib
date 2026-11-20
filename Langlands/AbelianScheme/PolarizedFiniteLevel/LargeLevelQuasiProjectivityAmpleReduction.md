# Eventual quasi-projectivity from ample line bundles

This internal module reduces the published target
`LargeLevelQuasiProjectivityStatement` to two named statements. It adds no
mathematical assertion beyond that implication. Both statements stay explicit
hypotheses.

## Result

`largeLevelQuasiProjectivity_of_ample` is a proved definition: a `def` whose
type is the proposition `LargeLevelQuasiProjectivityStatement`. It takes two
hypotheses:

- `Himm : Picard.AmpleHQuasiProjectiveStatement.{0}`. This is the general
  algebraic-geometry statement, in universe zero: a scheme that is locally of
  finite type over `Spec R` and carries an ample line bundle is H-quasi-projective
  over `R` (Stacks Lemma 29.40.3, Tag 01VS).
- `Hample : LargeLevelAmpleStatement`. This is the moduli statement: for
  sufficiently large `n`, every representing level base is locally of finite type
  over `Spec ℤ[1/n]` and carries an ample line bundle.

## Proof

Fix `P`, `g`, `d` with `0 < g` and `0 < d`. `Hample` gives a bound `N`, which
is also the bound for the target. Let `n ≥ N` with `3 ≤ n`, and let `X` be a
level base with a natural isomorphism `e` from its functor of points to
`moduliFunctor P g d n hd hn`.

1. `Hample`, applied to `X` and `e`, gives `LocallyOfFiniteType
   X.toLocalizationSpec` and an ample line bundle `L` on `X.obj`.
2. Ampleness includes compactness, `hL.compactSpace : CompactSpace X.obj`.
   Every morphism from a quasi-compact scheme to a quasi-separated scheme, such
   as the affine scheme `Spec ℤ[1/n]`, is quasi-compact (Mathlib instance
   `AlgebraicGeometry.quasiCompact_of_compactSpace`). This gives
   the first conclusion, `QuasiCompact X.toLocalizationSpec`.
3. `Himm`, applied with `R = ℤ[1/n]` (`Localization.Away (n : ℤ)`), the
   morphism `X.toLocalizationSpec`, step 1 and `L`, gives `m` and an immersion
   `i : X.obj ⟶ ProjectiveSpace ℤ[1/n] m` with
   `i ≫ projectiveSpaceToSpec ℤ[1/n] m = X.toLocalizationSpec`. The
   quasi-compactness of `i` that `IsHQuasiProjective` also provides is not
   needed.

The target's witnesses are `m` and `i`.

## Provenance

This is an internal derivation. It only combines the conclusions of the two
statements, which are documented in their own modules
(`Langlands.AlgebraicGeometry.Picard.AmpleHQuasiProjectiveStatement` and
`Langlands.AbelianScheme.PolarizedFiniteLevel.LargeLevelAmpleStatement`). The
module follows the pattern of `largeLevelRepresentability_of_chartCover` in
`LargeLevelRepresentabilityReduction`, whose fourth hypothesis is the target
`LargeLevelQuasiProjectivityStatement`.
