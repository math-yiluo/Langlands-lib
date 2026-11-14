# The `(𝔤𝔩_n(ℝ), O(n))`-module of a real standard module

Module: `Langlands.Representation.Archimedean.RealStandardModuleGKModule`.

## Purpose and provenance

This module is internal infrastructure for proving
`Langlands.Archimedean.RealLanglandsQuotientStatement`, the existence half of the Langlands
classification for `(𝔤𝔩_n(ℝ), O(n))`-modules (Knapp 1994, Theorem 1). The module
`Langlands.Representation.Archimedean.RealLanglandsQuotientReduction` reduces that statement to
`RealPrincipalSeriesQuotientStatement` and `RealLanglandsFromPrincipalSeriesStatement`. All three
ask for a nonzero linear map `B` with `IsRealStandardIntertwiner n ρ π ds B`. Each clause of that
predicate requires a right translate `R(k) f` (`k ∈ O(n)`) or a right derivative `R(X) f` of an
`O(n)`-finite function `f` of `realStandardModule n ds` to be again such a function. This module
proves these closure facts for every list of real blocks `ds`. It also packages the
`O(n)`-finite functions as a `(𝔤𝔩_n(ℝ), O(n))`-module in the exact sense of `IsRealGKModule`
(the Harish-Chandra module of the standard module), and shows that the identity map is an
`IsRealStandardIntertwiner` map.

It is the real analogue of the complex-standard-module part of
`Langlands.Representation.Archimedean.PrincipalSeriesGKModule`. The real case needs one extra
step because `realStandardModule n ds` is in general smaller than the principal series
`principalSeries ℝ n (realPositionCharacter ds)`: for each two-dimensional induction block it
imposes Fourier conditions along left rotations. The proofs only combine published Library
results:

- `rightTranslation_mem_principalSeries` and `rightDerivative_mem_principalSeries`
  (`PrincipalSeriesStability`): the principal series is stable under both operations;
- `rightTranslation_mem_realStandardModule`, `rightDerivative_mem_realStandardModule` and
  `realStandardModule_le_principalSeries` (`RealStandardModuleFourier`): both operations preserve
  the Fourier conditions as soon as the result lies in the principal series;
- `rightTranslation_mem_kFiniteFunctions`, `rightDerivative_mem_kFiniteVectors`
  (`PrincipalSeriesStability`) and `kFiniteRep`, `kFiniteLie`, `kFiniteLie_one_tmul_apply_coe`,
  `isRealGKModule_kFinite` (`PrincipalSeriesGKModule`): the `K`-finite functions of a
  right-translation-stable, right-derivative-stable space of smooth functions form a
  `(𝔤, K)`-module.

The mathematics is the standard fact that the `K`-finite vectors of a smooth representation form
a `(𝔤, K)`-module, applied to the Library definitions. The module makes no literature
assertion, so it has no literature sources. `realStandardRep` and `realStandardLie` are
auxiliary definitions of this formalization.

Notation: `GL_n(ℝ)` is `Langlands.GeneralLinear n ℝ` with manifold structure
`matrixModel ℝ n`; `O(n)` is the subgroup `unitaryCompact ℝ n`; `R(s)` is right translation
`Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ) s`, `(R(s) f)(g) = f(g s)`; and
`R(X) = rightDerivative (matrixModel ℝ n) X`.

## Declarations

### Stability of `realStandardModule`

- `rightTranslation_mem_realStandardModule_of_mem`: if `f ∈ realStandardModule N ds`, then
  `R(s) f ∈ realStandardModule N ds` for every `s ∈ GL_N(ℝ)`. Proof: `R(s) f` lies in the
  principal series (`rightTranslation_mem_principalSeries`), so
  `rightTranslation_mem_realStandardModule` applies.
- `rightDerivative_mem_realStandardModule_of_mem`: if `f ∈ realStandardModule N ds`, then
  `R(X) f ∈ realStandardModule N ds` for every real `N × N` matrix `X`. Proof: the same, with
  `rightDerivative_mem_principalSeries` and `rightDerivative_mem_realStandardModule`.
- `contMDiff_of_mem_realStandardModule`: every `f ∈ realStandardModule N ds` is smooth
  (`ContMDiff (matrixModel ℝ N) 𝓘(ℝ, ℂ) ∞ f`), the smoothness clause of the principal series.
- `rightTranslation_mem_kFiniteFunctions_realStandardModule n ds hf hk`: if
  `f ∈ kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)` and
  `k ∈ unitaryCompact ℝ n`, then `R(k) f` is again in that space. Proof:
  `rightTranslation_mem_kFiniteFunctions` with the stability of `realStandardModule` under all
  right translations.
- `rightDerivative_mem_kFiniteFunctions_realStandardModule n ds hf X`: under the same hypothesis
  on `f`, `R(X) f` is again in that space. Proof: membership in `realStandardModule` by the
  stability above; `O(n)`-finiteness by `rightDerivative_mem_kFiniteVectors`, which uses the
  smoothness of the functions of `realStandardModule` and their stability under right
  translation by `O(n)`.

### The `(𝔤, K)`-module

- `realStandardRep n ds : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) (kFiniteFunctions
  (realStandardModule n ds) (unitaryCompact ℝ n))` is right translation, defined as
  `kFiniteRep (realStandardModule n ds) _`. The matrix orthogonal group acts through
  `Unitary.toUnits`, so `realStandardRep_apply_coe` states
  `(realStandardRep n ds k f : GL_n(ℝ) → ℂ) = R(Unitary.toUnits k) f` (by `rfl`).
- `realStandardLie n ds : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ (kFiniteFunctions
  (realStandardModule n ds) (unitaryCompact ℝ n))` is the complex-linear extension
  `z ⊗ X ↦ z R(X)` of the right derivatives, defined as `kFiniteLie (realStandardModule n ds) _ _
  _`. `realStandardLie_one_tmul_apply_coe` states
  `(realStandardLie n ds (1 ⊗ₜ X) f : GL_n(ℝ) → ℂ) = R(X) f`.
- `isRealGKModule_realStandardModule n ds : IsRealGKModule n (realStandardRep n ds)
  (realStandardLie n ds)`: by `isRealGKModule_kFinite`.
- `isRealStandardIntertwiner_id n ds : IsRealStandardIntertwiner n (realStandardRep n ds)
  (realStandardLie n ds) ds LinearMap.id`. Proof: the membership witnesses of the two clauses
  are the two closure lemmas above. The equations follow from `realStandardRep_apply_coe` and
  `realStandardLie_one_tmul_apply_coe`, using that `Unitary.toUnits` of the orthogonal matrix
  underlying `k ∈ unitaryCompact ℝ n` is `k` (`Units.ext rfl`).

## Use

A proof of `RealLanglandsFromPrincipalSeriesStatement` or `RealPrincipalSeriesQuotientStatement`
that builds an intertwiner `B` from a composite of maps can obtain the existential membership
witnesses of `IsRealStandardIntertwiner` directly from
`rightTranslation_mem_kFiniteFunctions_realStandardModule` and
`rightDerivative_mem_kFiniteFunctions_realStandardModule`. Since these witnesses are proofs of
propositions, any two of them are equal. The pair `(realStandardRep n ds, realStandardLie n ds)`
is the Harish-Chandra module of the standard module, to which classical results about
`I(σ₁, …, σ_r)` are to be transferred.
