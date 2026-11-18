# Flatness at a maximal ideal from bijective truncated comparison maps

Author: Worker 387 (Task 7655).

This helper module is pure commutative algebra. It supplies the local flatness
criterion used for the chart-flatness proof
`Langlands.Analytic.AffineAnalytification.affineAnalytificationChartFlat`
(module `AffineAnalytificationChartFlatProof`, via `TatePolynomialFlatness`).
Everything lives in the namespace `Langlands.Analytic.TruncatedComparison`.
`R : Type u` and `S : Type v` are commutative rings with `Algebra R S`.

## Provenance

The results are standard commutative algebra and internal to this development.
They are not attributed to a literature statement. They package the step
"the completions of the two local rings agree, hence the map is flat" in the
proof of Berkovich 1990, Theorem 3.4.1(ii) (printed pp.63–64, PDF pp.77–78).
That proof asserts the isomorphism of completions at rigid points and deduces
flatness of the affinoid algebras over `A`. The Lean statements below are
exactly what the chart-flatness proof needs. They make no further claims.

## Declarations

- `quotientMap_bijective_of_le`: let `J ≤ 𝔟` be ideals of `R`. If the induced
  map `R ⧸ J → S ⧸ J S` is bijective, then so is `R ⧸ 𝔟 → S ⧸ 𝔟 S`.
  *Proof.* The inverse of the first map gives a ring map `ψ : S → R ⧸ J`
  with `ψ (algebraMap r) = [r]`. `ψ` sends `𝔟 S` into the image of `𝔟`.
  So if `algebraMap r ∈ 𝔟 S`, then `[r] ∈ 𝔟 ⧸ J` and `r ∈ 𝔟` because
  `J ≤ 𝔟`. This gives injectivity. Surjectivity lifts through the
  surjective first map, because `J S ≤ 𝔟 S`.
- `factor_evalₐ`: for `m ≤ n`, the evaluation of an element of the `I`-adic
  completion at level `n`, reduced modulo `I ^ m`, is its evaluation at level
  `m`.
- `pow_le_comap_pow`: if `𝔫 ≤ 𝔪 ∩ R`, then `𝔫 ^ k ≤ (𝔪 ^ k) ∩ R`.
- Under `h𝔫 : 𝔫 ≤ 𝔪.comap (algebraMap R S)` and the hypothesis `hbij` that
  every induced map `R ⧸ 𝔫 ^ k → S ⧸ 𝔪 ^ k` is bijective:
  - `truncEquiv k : (R ⧸ 𝔫 ^ k) ≃ₐ[R] (S ⧸ 𝔪 ^ k)` is that bijection.
    `factor_truncEquiv` and `factor_truncEquiv_symm` say it and its inverse
    commute with reduction from level `n` to level `m`.
  - `homComponent k` and `invComponent k` compose evaluation at level `k` with
    `truncEquiv k` and with its inverse. `homComponent_compat` and
    `invComponent_compat` say these families are compatible.
  - `completionHom` and `completionInv` are their limits, built with Mathlib's
    `AdicCompletion.liftAlgHom`. `evalₐ_completionHom` and
    `evalₐ_completionInv` describe their evaluations.
  - `completionEquiv : AdicCompletion 𝔪 S ≃ₐ[R] AdicCompletion 𝔫 R`. Both
    composites are the identity, which is checked levelwise with
    `AdicCompletion.ext_evalₐ`.
- `flat_localization`: suppose in addition that `R` and `S` are Noetherian and
  `𝔪` is maximal. Then `Localization.AtPrime 𝔪` is flat over `R`.
- `flat_of_forall_maximal`: `S` is flat over `R` if `Localization.AtPrime 𝔪` is
  flat over `R` for every maximal ideal `𝔪` of `S`. This is Mathlib's
  `Module.flat_of_isLocalized_maximal`.

## Proof of `flat_localization`

Let `T = AdicCompletion 𝔪 S`.

1. `T` is flat over `R`. Through `completionEquiv` it is isomorphic, as an
   `R`-module, to the adic completion of the Noetherian ring `R`, which Mathlib
   knows is flat.
2. `T` is a local ring. `𝔪` is finitely generated, so `T` is adically complete
   for `𝔪 T` (`AdicCompletion.isAdicComplete_self`), and `𝔪 T` is maximal
   (`AdicCompletion.isMaximal_map_of_le`). Mathlib's
   `isLocalRing_of_isAdicComplete_maximal` then applies.
3. Elements `s ∉ 𝔪` become units in `T`. Maximality gives `y` and `i ∈ 𝔪` with
   `y s = 1 - i`, and `i` maps into the Jacobson radical of `T`
   (`IsAdicComplete.le_jacobson_bot`). Hence `S → T` factors through
   `S_𝔪 = Localization.AtPrime 𝔪` (`IsLocalization.lift`), compatibly with the
   `S`- and `R`-algebra structures.
4. `T` is flat over `S` (`AdicCompletion.flat_of_isNoetherian`), so it is flat
   over `S_𝔪` (`Module.flat_iff_of_isLocalization`). The map `S_𝔪 → T` is local,
   because the maximal ideal of `S_𝔪` generates `𝔪 T`, which is the maximal
   ideal of `T`. A flat local homomorphism of local rings is faithfully flat
   (`Module.FaithfullyFlat.of_flat_of_isLocalHom`).
5. The Library's `Langlands.Analytic.flat_of_faithfullyFlat_target`
   (module `FlatTargetDescent`) descends flatness over `R` from `T` to `S_𝔪`.

## Scope

The criterion needs only `𝔫 ≤ 𝔪 ∩ R`, not that `𝔫` is maximal or equal to
`𝔪 ∩ R`, together with bijectivity at every level `k`. Universes of `R` and
`S` are independent.
