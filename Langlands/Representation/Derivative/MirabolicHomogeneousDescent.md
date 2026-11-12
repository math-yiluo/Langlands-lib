# Homogeneity descends through mirabolic `Φ⁻`

Module `Langlands.Representation.Derivative.MirabolicHomogeneousDescent`.

This helper module supplies the homogeneity inputs of Bernstein, *P-invariant
distributions on GL(N) and the classification of unitary representations of GL(N)
(non-archimedean case)*, Lie Group Representations II, LNM 1041 (1984), §7.4 (PDF
p. 34). Bernstein uses that the restriction `π|P` of an irreducible representation to
the mirabolic subgroup is homogeneous (Zelevinsky 1980, Theorem 6.2 / §7). Hence the
mirabolic representation `τ = (Φ⁻)^(k-1)(π|P)` has no nonzero vector fixed by the
whole radical whenever `π` has a nonzero derivative of order greater than `k`. All
statements use the Library notions `level T ψ` (highest nonzero derivative order of a
mirabolic representation) and `IsHomogeneous T ψ` (every nonzero subrepresentation
has the same level as the whole).

All theorems are in namespace `Langlands.Derivative.Mirabolic`, with
`T : F.TopologicalData` and a unitary additive character `ψ`.

## Statements

- `level_phiMinus_add_one T ψ W`: for `W` on `mirabolic (M + 1) F` with
  `2 ≤ level W`, `level (Φ⁻ W) + 1 = level W`.
- `isHomogeneous_phiMinus T ψ B`: if `B` on `mirabolic (M + 1) F` is homogeneous with
  `2 ≤ level B`, then `Φ⁻ B` is homogeneous and `level (Φ⁻ B) + 1 = level B`.
- `isHomogeneous_phiMinusIterate T ψ n j B`: if `B` on `mirabolic (n + j) F` is
  homogeneous with `j + 1 ≤ level B`, then `(Φ⁻)^j B = (phiMinusIterate T ψ n j).obj B`
  is homogeneous and `level ((Φ⁻)^j B) + j = level B`.
- `eq_zero_of_radical_fixed T ψ A`: if `A` on `mirabolic (M + 1) F` is homogeneous
  with `2 ≤ level A`, then every vector of `A` fixed by all of
  `radical (M + 1) F` is zero.
- `isHomogeneous_restriction_of_isIrreducible T ψ π`: for an irreducible smooth
  representation `π` of `GL_(N+1)(F)` (vector-space universe `max uF uV`), the
  mirabolic restriction `(generalLinearRestriction T N).obj π` is homogeneous.

## Proofs

- `level_phiMinus_add_one`: `Φ⁻ W` is nonzero because `level W ≥ 2`
  (`LevelCalculus.nontrivial_phiMinus_iff`), so its level is positive and
  `LevelCalculus.level_eq_level_phiMinus_succ` gives the identity.
- `isHomogeneous_phiMinus`: for a nonzero subrepresentation `X` of `Φ⁻ B`, the
  Library's `HighestLayer.liftStep` gives a subrepresentation `W` of `B` with
  `imageStep W = X` (`HighestLayer.imageStep_liftStep`). `W` is nonzero, since
  otherwise its image would be `⊥` (`HighestLayer.imageStep_bot`). By homogeneity
  `level W = level B ≥ 2`. `HighestLayer.phiMinusSubIso` identifies `Φ⁻ W` with `X`,
  so `level X = level (Φ⁻ W) = level W - 1 = level B - 1 = level (Φ⁻ B)` by two
  applications of `level_phiMinus_add_one`.
- `isHomogeneous_phiMinusIterate`: induction on `j`, using that
  `phiMinusIterate T ψ n (j + 1)` is definitionally
  `phiMinus T ψ (n + j) ⋙ phiMinusIterate T ψ n j`.
- `eq_zero_of_radical_fixed`: the radical-fixed vectors form a subrepresentation
  `U` (the radical is normal in the mirabolic group). If `v ≠ 0` is radical-fixed,
  `U ≠ ⊥`, so homogeneity gives `level U = level A ≥ 2`. But `Φ⁻ U = 0`. By
  `HighestLayer.exists_radical_difference`, every `Φ⁻`-class is
  `c • q (ρ u w - w)` for some radical element `u`, and this vanishes on `U`. So
  `LevelCalculus.level_le_one_of_subsingleton_phiMinus` gives `level U ≤ 1`, a
  contradiction.
- `isHomogeneous_restriction_of_isIrreducible`: by
  `Classification.multisegmentSocleExhaustion`, `π` embeds into a product `d.induced`
  of segment socles whose segments are precedence ordered.
  `Classification.precedenceOrdered_endpointSeparated` (with
  `cuspidalIntegralTwistFreeness`) makes them endpoint separated. Then
  `Classification.segmentSocleProductHomogeneity` and `isGeneralLinearHomogeneous_iff`
  make the mirabolic restriction of `d.induced` homogeneous. Restriction is exact
  (`generalLinearRestriction_mapsShortExact`), so it preserves the embedding.
  `LevelCalculus.isHomogeneous_of_forall_injective` and
  `LevelCalculus.level_eq_of_isHomogeneous` then transfer homogeneity to the
  restriction of `π`, since every nonzero subrepresentation of it embeds into the
  homogeneous restriction of `d.induced`.
