# A maximal torus of the preimage of a subgroup in a central cover

Author: Worker 1413.

Module `Langlands.GroupScheme.SimplyConnected.CoverPreimageTorus`, namespace
`Langlands.GroupScheme.CoverPreimage`, over a field `k`. Internal helpers for
clause 6 of the reduction
[`SplitTorusCentralizerCoverPreimageReduction`](SplitTorusCentralizerCoverPreimageReduction.md).
They introduce no literature assertion. Notation as in
[`CoverPreimageCharacters`](CoverPreimageCharacters.md).

- `isSplitTorus_baseChange_of_flat_surjective`. Let `pr : T ⟶ T'` be a flat,
  surjective homomorphism of commutative group schemes with `T'` a torus. If
  `T` splits over a field extension `E/k`, then so does `T'`. The base change
  of `pr` (published `baseChange_map_isPullback`) is surjective onto the
  smooth, hence reduced, torus `T'_E`. It is therefore schematically
  dominant, and the published `IsSplitTorus.of_schematicallyDominant_hom`
  applies.
- `exists_maximalTorus_preimage`. Assume: `d` and `j` are monomorphic; `π` is
  a central isogeny; `i : Z ⟶ G` is central with `Z` a torus and
  `centralProduct i d` a central fppf cover; `iM ≫ j = i`; `M` and `M'`
  are connected reductive; and `t : T ⟶ M` is a maximal torus. Then there
  are a maximal torus `t' : T' ⟶ M'` and `g : T' ⟶ T` with `t' ≫ p = g ≫ t`.
  Moreover, `T'` splits over every field extension of `k` over which `T`
  splits.
  - *`Z ⊆ T`.* `iM` commutes with `t`, so it factors through `t`
    (`IsMaximalTorus.exists_factor_of_commute`,
    [toolkit](CoverPreimageToolkit.md)), as `zt ≫ t = iM`.
  - *Power lifts.* The published power lift through the restricted product
    `ρ : Z × (D ×_G M) ⟶ M` gives `Φ` with `Φ ≫ ρ = [2N] ≫ t`. A second
    power lift through `toDerivedPart` gives `Φ' : T ⟶ M'` with
    `Φ' ≫ toDerivedPart = [2N₃] ≫ Φ₂`, where `Φ₂` is the second component of
    `Φ`. With `n = 2N₃ · 2N`, every point `y` of `T` satisfies
    `t(yⁿ) = iM(z(y)) · p(Φ'(y))` for a point `z(y)` of `Z`.
  - *`T'`.* `T'` is the schematic image of `Φ'`. It is a torus with closed
    inclusion `t'`, and the projection `pr : T ⟶ T'` is flat, surjective and
    schematically dominant. The displayed identity puts `p(Φ'(y))` in the range
    of `t`, since `iM = zt ≫ t`. The published
    `SubgroupFunctor.range_comp_le_iff_of_isSchemeTheoreticallyDominant`
    removes `pr`. `g` is the factorization of `t' ≫ p` through `t`
    (published `IsRepresentedBy.liftOfLE`).
  - *Splitting.* `isSplitTorus_baseChange_of_flat_surjective` applied to `pr`.
  - *Maximality.* Let `t' = f ≫ t''` with `t'' : T'' ⟶ M'` a closed torus.
    - By the displayed identity, every point of `T` composed with the power
      map `[n]` is a central point times `p(Φ'(y))`, and `Φ'` factors through
      `t''`. So `t'' ≫ p` commutes with `[n] ≫ t`. By
      `torusCentralizer_comp_of_fpqc`, it commutes with `t`. Hence
      `t'' ≫ p = γ ≫ t` for some `γ`.
    - Let `c` be a point of `T''` and `y = γ(c)`. The point
      `w = t''(cⁿ) · t''(f(pr(y)))⁻¹` of `M'` satisfies `p(w) = iM(z(y))`.
      So `(z(y)⁻¹, toDerivedPart(w))` is killed by `ρ`, and its `N`-th power is
      trivial. Then `w^N` is killed by `toDerivedPart`, so `w^{N N₃} = 1`.
      Since `t''` is monomorphic and `T''` commutative, this gives
      `t''(c^{n N N₃}) = t'(pr(y)^{N N₃})`.
    - So `[n N N₃] ≫ t''` factors through `t'`. The published
      `exists_factor_of_multiplication_comp` (module
      `CentralIsogeny.MaximalTorusImageProof`) then factors `t''` itself as
      `φ' ≫ t'`. Cancelling the monomorphisms `t'` and `t''` shows that `φ'`
      is inverse to `f`.
