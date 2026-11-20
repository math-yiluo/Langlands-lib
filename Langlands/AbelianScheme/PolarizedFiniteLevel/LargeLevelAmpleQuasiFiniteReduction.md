# Eventual ample line bundles from finite type, separatedness and a quasi-finite projective map

The module `Langlands.AbelianScheme.PolarizedFiniteLevel.LargeLevelAmpleQuasiFiniteReduction`
contains one proved definition,
`Langlands.AbelianScheme.PolarizedFiniteLevel.largeLevelAmple_of_quasiFiniteProjective`,
of type

`Picard.QuasiFiniteAmplePullbackStatement.{0} → LargeLevelFiniteTypeStatement →
LargeLevelSeparatedStatement → LargeLevelQuasiFiniteProjectiveStatement →
LargeLevelAmpleStatement`.

It is an internal derivation and makes no external mathematical claim.

## The proof

Fix `P`, `g`, `d` with `0 < g` and `0 < d`. The three moduli statements give
bounds `N₁`, `N₂`, `N₃`. The definition uses `max N₁ (max N₂ N₃)`. Let `n` be at
least this bound, with `3 ≤ n`, and let `X : LevelBase n` represent the moduli
functor. Write `π = X.toLocalizationSpec` and
`p = projectiveSpaceToSpec ℤ[1/n] m`.

1. `LargeLevelFiniteTypeStatement` gives that `π` is locally of finite type and
   quasi-compact. `LargeLevelSeparatedStatement` gives that `π` is separated.
2. `LargeLevelQuasiFiniteProjectiveStatement` gives `m` and a locally
   quasi-finite `j : X.obj ⟶ ProjectiveSpace ℤ[1/n] m` with `j ≫ p = π`.
3. `p` is separated, because the Library instance `projectiveSpaceToSpec_isProper`
   (module `Langlands.AlgebraicGeometry.ProjectiveSpace.Structure`) makes it proper.
   Rewriting `j ≫ p = π` moves the properties of step 1 to `j ≫ p`. Mathlib's
   cancellation lemmas then give them for `j`:
   - `locallyOfFiniteType_of_comp` gives that `j` is locally of finite type;
   - `QuasiCompact.of_comp` gives that `j` is quasi-compact, since `p` is
     quasi-separated;
   - `IsSeparated.of_comp` gives that `j` is separated.
4. The Library theorem `projectiveSpaceTwistOneAmple` gives an ample line bundle
   `M` on `ProjectiveSpace ℤ[1/n] m` whose underlying module is `𝒪(1)`.
5. `QuasiFiniteAmplePullbackStatement.{0}`, applied to `j` and `M`, gives that
   the pullback `(LineBundle.pullback j).obj M` is ample. With the local finite
   type of `π` from step 1, this is the conclusion of `LargeLevelAmpleStatement`.

## Role

The premises split the moduli content of `LargeLevelAmpleStatement` into three
independent properties of the representing scheme. They are boundedness (finite
type), separatedness, and a projective map with finite fibres. The fourth
premise is general algebraic geometry (Stacks Lemmas 37.43.2 and 29.38.7).
With `largeLevelQuasiProjectivity_of_ample`, the published target
`LargeLevelQuasiProjectivityStatement` follows from these premises and
`Picard.AmpleHQuasiProjectiveStatement`.
