# JPSS integrals along an isomorphism of topological fields

Author: Worker 5731. This is a supporting lemma module for the proof of
`Langlands.Global.PoleComparison.HenniartCompositeFactorStatement` (Task 5230).
It states no new published mathematics: it checks that the Rankin–Selberg
integrals of Jacquet, Piatetski-Shapiro and Shalika, as formalized in
`Langlands.Representation.RankinSelberg.QuotientIntegrals` and
`FunctionalEquationStatement`, are unchanged when every object is transported
along an isomorphism of topological fields.

## Setting

In namespace `Langlands.RankinSelberg.FieldTransport`, fix topological fields
`F` and `E` and a ring isomorphism `σ : F ≃+* E` with `hσ : Continuous σ` and
`hσs : Continuous σ.symm`. Write `T = fieldEquiv n σ hσ hσs : GL_n(F) ≃ₜ* GL_n(E)`
for the published entrywise isomorphism of
`Langlands.VirtualRepresentation.Supercuspidal.FieldTransport`.

All comparisons are relational. Instead of constructing the transported
function, a hypothesis states that an `E`-side function composed with the
entrywise map equals the given `F`-side function, for example
`hW : ∀ g, W₂.val (T g) = W.val g`. Likewise unitary additive characters `ψ` of
`F` and `ψ'` of `E` are related by `hψ : ∀ x, ψ' (σ x) = ψ x`, absolute values by
`habv : ∀ x, abv' (σ x) = abv x`, and additive Haar measures by
`hν : ν'.measure = ν.measure.map σ`. This avoids rewriting inside dependent
types.

## Matrices

- `fieldEquiv_mem_upperUnipotent_iff` shows `T g` is upper unipotent exactly when
  `g` is: an entry is `0` or `1` exactly when its image under `σ` is.
  `unipotentEquiv σ hσ hσs n` is the resulting isomorphism of the published
  subgroups `upperUnipotent n`, built with `subgroupEquiv` from the module
  `FieldTransport.Group`; `unipotentEquiv_apply_coe` records its value.
- `det_fieldEquiv`: `det (T g) = σ (det g)` (Mathlib's `RingHom.map_det`).
- `fieldEquiv_permutation`, `fieldEquiv_weylLong`, `fieldEquiv_blockWeylAt`,
  `fieldEquiv_neg_one`: `T` fixes permutation matrices, the long Weyl element
  `weylLong`, the block Weyl element `blockWeylAt n r hnr` (which the published
  `UnequalRankComplementaryConjugationProof.blockWeylAt_eq` identifies with a
  permutation matrix) and `-1`, because `σ` fixes `0`, `1` and `-1`.
- `fieldEquiv_inverseTranspose`: `T` commutes with the published
  `inverseTranspose` (definitional).
- `lastRow_fieldEquiv`: the last row of `T g` is `σ` applied to the last row
  of `g`.
- `unequalRankMatrix_fieldEquiv`: the published block matrix
  `unequalRankMatrix j k` of the unequal-rank integral, built from `T g` and the
  entrywise image `x.map σ` of a rectangular matrix, is `T` of the block matrix
  built from `g` and `x`. The proof compares entries of `appendIdentity` and of
  the rectangular block.
- `determinantWeight_fieldEquiv`: the published weight `|det g|^s` is preserved,
  by `det_fieldEquiv` and `habv`.

## Characters

Assume `hψ : ∀ x, ψ' (σ x) = ψ x`.

- `standardCharacter_unipotentEquiv`: the published standard character
  `standardCharacter ψ' n` of the upper unipotent group of `GL_{n+1}(E)`,
  evaluated at the image of `u`, equals `standardCharacter ψ n u`; the
  superdiagonal sum is mapped by `σ`. `inverseStandardCharacter_unipotentEquiv`
  is the same for the inverse character.
- `scale_neg_one_apply`: `ψ'.scale (-1) (σ x) = ψ.scale (-1) x`, so the
  relation `hψ` also holds for the characters `x ↦ ψ (-x)`, which the published
  dual functions `firstDualFunction` and `secondDualFunction` use.
- `complex_apply_map`: the same relation for the complex values of `ψ` and `ψ'`.

## Quotients and integrals

- `quotientHomeomorph σ hσ hσs n` is the homeomorphism of the published left
  unipotent quotients `LeftUnipotentQuotient n F ≃ₜ LeftUnipotentQuotient n E`
  induced by `T` on `GL_{n+1}`, an instance of `cosetHomeomorph` of
  `FieldTransport.Group`. `quotientHomeomorph_mk` gives it on cosets, and
  `map_quotientHomeomorph` rewrites pushforward along it as pushforward along a
  measurable equivalence.
- `equalRankIntegrand_quotientHomeomorph`: if `W₂ ∘ T = W`, `W₂' ∘ T = W'` for
  Whittaker functions `W`, `W₂` and inverse Whittaker functions `W'`, `W₂'`,
  and `Φ₂ ∘ σ = Φ` for row Schwartz–Bruhat functions (entrywise `σ`), then the
  published equal-rank integrand
  `W(g) W'(g) Φ(e_n g) |det g|^s` over `E`, evaluated at the image of a coset,
  equals the one over `F` at the coset. `unequalRankIntegrand_quotientHomeomorph`
  is the analogue for the unequal-rank integrand at `x.map σ`.
- For a measure `μ` on `LeftUnipotentQuotient n F`, `equalRankIntegral_map` and
  `equalRankConverges_map_iff` state that the published `equalRankIntegral`
  and `EqualRankConverges` over `E` for the measure
  `μ.map (quotientHomeomorph σ hσ hσs n)` and the transported functions equal,
  respectively are equivalent to, those over `F` for `μ`. The proofs are the
  change of variables `integral_map_equiv` and `integrable_map_equiv`.
- `matrixMeasurableEquiv σ hσ hσs j t` is the entrywise map of `j × t` matrices
  as a measurable equivalence (`matrixMeasurableEquiv_apply`), and
  `measurePreserving_matrixMeasurableEquiv` shows that it carries the published
  product measure `rectangularMeasure ν j t` to `rectangularMeasure ν' j t`
  when `hν` holds and `ν'` is σ-finite (`measurePreserving_pi`).
- `unequalRankIntegral_map`, `unequalRankConverges_map_iff` and
  `unequalRankIntegralAt_map` give the corresponding statements for the
  published unequal-rank integral, its convergence predicate and the
  rank-indexed `unequalRankIntegralAt j k hr` (where `hr : r = n + (j + k + 1)`
  is eliminated by `subst`). Convergence uses `integrable_map_prod_map_iff` from
  `FieldTransport.Group`, which needs s-finiteness of the matrix measure only
  and none of the quotient measure `μ`; the scalar measures `ν` and `ν'` are
  assumed σ-finite.

## Dual and translated Whittaker functions

- `firstDualFunction_fieldEquiv` and `secondDualFunction_fieldEquiv`: the
  published transformed functions of the functional equation, which evaluate
  `f` at a product of `weylLong` and the inverse transpose of the argument,
  satisfy the same relation as `f` and `f₂`, because `T` is multiplicative,
  commutes with the inverse transpose and fixes `weylLong`.
- `translateWhittaker_fieldEquiv`: the right translate of `f₂` by `T a`,
  composed with `T`, is the right translate of `f` by `a`.

## Row Fourier transform

- `rowMeasurableEquiv σ hσ hσs d` is the entrywise map `F^d → E^d` as a measurable
  equivalence; `measurePreserving_rowMeasurableEquiv` shows it carries the
  published `rowMeasure ν d` to `rowMeasure ν' d` under `hν`.
- `rowPairing_map`: the published bilinear pairing `∑ x_i y_i` is mapped by `σ`.
- `rowFourierIntegral_map`: if `Φ₂ ∘ σ = Φ` entrywise then the published
  `rowFourierIntegral ψ' ν' d Φ₂` at `σ y` equals `rowFourierIntegral ψ ν d Φ`
  at `y`, by change of variables and `complex_apply_map`.
- `isRowFourierPair_map_iff`: the published `IsRowFourierPair ψ' ν' Φ₂ Φhat₂`
  holds exactly when `IsRowFourierPair ψ ν Φ Φhat` holds, for transported
  `Φ₂`, `Φhat₂`. Every point of `E^d` is the entrywise image of a point of
  `F^d`.
- `rowTestEquiv σ hσ hσs d` is the complex-linear equivalence of row
  Schwartz–Bruhat spaces `Φ ↦ Φ ∘ σ⁻¹`, from the published
  `Hecke.TestFunction.pullback`; `rowTestEquiv_apply_map` and
  `rowTestEquiv_symm_apply` give its values.
