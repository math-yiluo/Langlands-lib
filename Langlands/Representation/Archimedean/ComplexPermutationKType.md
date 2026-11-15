# `U(n)`-equivariant maps between complex principal series

Module `Langlands.Representation.Archimedean.ComplexPermutationKType`, namespace
`Langlands.Archimedean.ComplexPermutation`. This internal helper module for
`ComplexStandardPermutationStatement` has no literature source.

`KF n ds` abbreviates `kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n)`, the
`U(n)`-finite functions `X(ds)` of the standard module of `ds`. `U(n)` acts by right translation
(`complexStandardRep n ds`).

## The two hypotheses of `ComplexPermutationEndomorphism`

* `kFiniteEval_one_separating`: if `(ρ(k) f)(1) = f(k)` vanishes for every unitary `k`, then
  `f = 0`. This is the Library lemma `ComplexDuality.eq_zero_of_mem_principalSeries_of_eqOn`
  (Iwasawa decomposition `GL_n(ℂ) = B · U(n)`).
* `isFiniteVector_complexStandardRep`: every vector of `X(ds)` is a finite vector. This is the
  first clause of `isComplexGKModule_complexStandardModule`.

## The invariant form

`unitaryForm n ds f h = ∫_{U(n)} f(k) conj(h(k)) dk`, for the Haar probability measure
`ComplexDuality.unitaryHaar n`. It is a sesquilinear form `X(ds) →ₗ[ℂ] X(ds) →ₗ⋆[ℂ] ℂ`; the
integrands are continuous on the compact group, hence integrable (`integrable_mul_conj`).

* `unitaryForm_invariant`: invariance under right translation by `U(n)`, by right invariance of
  the Haar measure of the compact group `U(n)`.
* `unitaryForm_self_eq_zero`: `⟨f, f⟩ = ∫ |f|² = 0` forces `f = 0`. Otherwise `|f|²` is a
  continuous nonnegative function on `U(n)` that is nonzero somewhere, and its integral is
  positive (`ComplexDuality.integral_unitaryHaar_pos`). So `f` vanishes on `U(n)`, hence
  everywhere.

## Upgrade lemmas

* `surjective_of_injective_endo`, `injective_of_surjective_endo`: the two results of
  `ComplexPermutationEndomorphism` for `W = X(es)`.
* `surjective_of_injective_of_kMap`: if `Φ : X(es) → X(ds)` is an injective `U(n)`-equivariant
  linear map, every injective `U(n)`-equivariant `S : X(ds) → X(es)` is surjective, because
  `S ∘ Φ` is an injective equivariant endomorphism of `X(es)`.
* `injective_of_surjective_of_kMaps`: if `Φ₁ : X(ds) → X(es)` and `Φ₂ : X(es) → X(ds)` are
  injective and `U(n)`-equivariant, every surjective `U(n)`-equivariant `S : X(es) → X(ds)` is
  injective. By the previous lemma `Φ₁` is surjective; then `Φ₁ ∘ S` is a surjective equivariant
  endomorphism of `X(es)`, hence injective, and so is `S`.
