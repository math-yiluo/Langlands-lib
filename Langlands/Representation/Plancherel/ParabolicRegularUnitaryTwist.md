# Regular unitary unramified twists on the literal Levi

Author: Worker 1597.

## Source

The argument is the separation of central characters in the proof of the
Theorem of VI.8.5 in D. Renard, *Représentations des groupes réductifs
p-adiques*, French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`, printed
p.194 / PDF p.200. For a unitary unramified `ψ` outside a Zariski-closed subset
of `Im X(M)`, the central characters of `ρ ⊗ ψ` and of `w · (ρ ⊗ ψ)` differ for
every nontrivial `w ∈ W(M, M)/W_M`. The proof cites the faithful action of
`W(M, M)/W_M ≃ W(A)` on `𝔞*` (V.4.3.3, V.3.5) and the description of
`Im X(M)` (V.3.20). Waldspurger 2003, IV.3 (printed p.285 / PDF p.51,
`waldspurger-2003-plancherel`), uses the existence of a regular point of the
unramified orbit of a square-integrable `π` to apply Proposition IV.2.2.

## The statement

`RegularUnitaryTwistExistenceStatement` is a derived Prop. The context is a
nonarchimedean local field `F` of any characteristic, a connected reductive `G`
with canonical point topology whose point group is nonarchimedean, and a
`ParabolicRootPresentation r` of the actual rational parabolic `p`, Levi `l`
and split component `a`, as in `ConditionalParabolicGenericIrreducibilityStatement`.
Write `Mpt = parabolicLeviPointSubgroup p l`. For a nontrivial smooth
representation `π` of `Mpt` with a central character `ω`, it asserts that some
unramified character `χ` of the full rational-norm family has `‖χ m‖ = 1` for
all `m` and makes `π.twist χ` `IsNormalizerRegular`. Regularity is taken for
the literal normalizer of `Mpt` in `G(F)`. The statement only asserts existence.
It says nothing about the Zariski-closed exceptional set or about the
geometric lemma.

`regularUnitaryTwistExistence` proves this statement. No hypothesis is added.

## Proof

- `exists_leviIso_of_mem_normalizer`: an element `g` of the abstract normalizer
  of `Mpt` in `G(F)` normalizes `M` as a group scheme. There is `φ : M ≅ M` with
  `φ ≫ l ≫ p = l ≫ p ≫ int(g)`. The proof uses the published
  `hasDenseRationalPoints_of_localField`: a smooth connected affine group over
  a local field has dense rational points. Then
  `SubgroupFunctor.range_le_of_dense_rationalPoints`, applied to `M` and to
  conjugation by `g` and by `g⁻¹`, gives equal subgroup functors. Finally
  `IsRepresentedBy.isoOfIsRepresentedBy` produces `φ`.
- `rationalPoints_map_comp_innerIso`, `rationalPoints_map_iso_mem_center` and
  `twist_hasCentralCharacter` are small helpers: points under `l ≫ p ≫ int(g)`,
  automorphisms preserving central points, and the product central character
  `ψ|_Z · ω` of a twist.
- `unramifiedEvaluationRegular_sub_algebraMap_ne_zero`: if some rational
  character `α` has `‖α(b)‖ ≠ 1`, then for every constant `κ` the regular
  function `χ ↦ χ(b) − κ` on unramified characters is nonzero. It takes the
  values `1 − κ` at the trivial character and `‖α(b)‖ − κ` at the positive
  character `‖α‖`. The latter is continuous because the norm character is
  locally constant.
- `exists_unitary_twist_isNormalizerRegular`. The presentation `r` supplies
  the dynamic presentation of `p`. Worker 1739's
  `exists_finite_normalizer_representatives_of_dynamicParabolic` then gives
  finitely many normalizing points `g_t`, with automorphisms `φ_t`, such that
  every scheme normalizer is some `g_t` times a Levi point. If `g_t ∉ Mpt`,
  `mem_pointImage_of_normalizes_of_norm_of_dynamicParabolic` gives a central
  point `x_t` of `M(F)` and a rational character `α_t` with
  `‖α_t(φ_t x_t)‖ ≠ ‖α_t(x_t)‖`. For such `t` the function
  `f_t(χ) = χ(φ_t(x_t) x_t⁻¹) − ω(x_t) ω(φ_t x_t)⁻¹` is nonzero. The published
  `rationalUnramifiedRegular_exists_unitary_finset_ne_zero` gives a unitary
  unramified `χ` on `M(F)` at which all of them are nonzero. Transported to
  `Mpt` by `parabolicLeviUnramifiedCharactersHomeomorph`, this is the
  character. Now let `g` be a normalizer element outside `Mpt` whose conjugate
  central character agrees with `ψ|_Z · ω`. By the first item, `g = g_t · m`
  with `g_t ∉ Mpt`. Conjugation by `g` sends the image of `φ_t x_t` to that of
  `x_t`, because `x_t` is central. Evaluating the equality there forces
  `f_t(χ) = 0`, a contradiction. The published
  `isNormalizerRegular_of_centralCharacter` concludes.

## Dependencies and a correction

The module imports `DynamicLeviNormalizer` and its helpers
`FiniteNormalizerRepresentatives`, `LeviNormalizerBridge` and
`SplitComponentNormRigidity`. They are Worker 1739's approved but unpublished
candidate `7e5d7c99` for task `822bbd74`, used unchanged. The same submission
renames the anonymous local topology instance of the published
`RationalUnitaryNonvanishing.lean` to `rationalUnitaryNonvanishingPointTopology`.
Its auto-generated global name coincided with the one generated in the
published `ParabolicGenericIrreducibilityStatement.lean`, so no module could
import both. No declaration, statement or proof there changes.
