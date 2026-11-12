# Algebraic input for finite normalization covers

Author: Worker 185.

This is a helper module for the proof `Langlands.AlgebraicGeometry.LangWeil.finiteNormalizationCover`
of `Langlands.AlgebraicGeometry.LangWeil.FiniteNormalizationCoverStatement` (module
`FiniteNormalizationCoverProof`). Its declarations are in the namespace
`Langlands.AlgebraicGeometry.LangWeil.NormalizationCoverConstruction`. It contains two
commutative-algebra inputs:

- a chain of primes of the expected length in each fibre of a finite injective map from a
  polynomial algebra;
- generic Noether normalization over a domain, in the form of a finite injective map from a
  polynomial algebra after inverting one nonzero element of the base.

Provenance: internal helper results with no literature claim of their own. The normalization
input is the Library theorem
`Algebra.exists_ne_zero_algebraicIndependent_forall_isIntegral_pow_smul_of_finiteType` (module
`Langlands.AnthropicFLT.Theorems.Thm_Algebra_exists_ne_zero_algebraicIndependent_forall_isIntegral_pow_smul_of_finiteType`),
which is imported. The other steps use Mathlib's lying-over and going-up theorems for integral
extensions.

## A chain of primes in a polynomial algebra (section `Chain`)

Fix a commutative ring `K`, a prime `𝔭` of `K` and `d : ℕ`. The variables of the polynomial
algebra are indexed by `ULift (Fin d)`, as in the statement's relative affine space.

- `killMap d 𝔭 k : K[X] →+* (K ⧸ 𝔭)[X]` reduces coefficients modulo `𝔭` and sends `Xᵢ` to `0`
  when `i < k`, and to `Xᵢ` otherwise.
- `killMap_succ` writes `killMap (k + 1)` as `killMap k` followed by the evaluation that also
  kills the variables of index `k`. `killMap_comp_C` says that on constants `killMap k` is the
  quotient map `K → K ⧸ 𝔭`. Hence `comap_ker_killMap`: the kernel of `killMap k` contracts to
  `𝔭` along `C : K → K[X]`.
- `ker_killMap_lt`: for `i < d`, the kernel at stage `i` is strictly smaller than at stage
  `i + 1`. The inclusion follows from `killMap_succ`. The variable `X_i` lies in the larger
  kernel but not the smaller one, because `K ⧸ 𝔭` is nontrivial.
- `polyChain d 𝔭` is the strictly increasing series of length `d` whose `k`-th term is the
  kernel of `killMap k`, that is `𝔭[X] + (X₀, …, X_{k-1})`. Its terms are prime because
  `(K ⧸ 𝔭)[X]` is a domain. `polyChain_length` records the length and `comap_polyChain` says
  that every term contracts to `𝔭`.

`exists_ltSeries_fibre` proves: if `ψ : K[X] →ₐ[K] E` (with `d` variables) is integral and
injective, then over every prime `𝔭` of `K` there is a strictly increasing series of primes of
`E` of length `d`, each of which contracts to `𝔭` in `K`. The proof makes `E` a `K[X]`-algebra
through `ψ`. Since `ψ` is injective, its kernel `⊥` is contained in the first term of
`polyChain d 𝔭`, so lying over (`Ideal.exists_ideal_over_prime_of_isIntegral`) gives a prime of
`E` over that first term. Going up (`Ideal.exists_ltSeries_of_hasGoingUp`) extends it to a series
of the same length whose contractions to `K[X]` are the terms of `polyChain d 𝔭`. Since
`ψ ∘ C` is the structure map `K → E`, each term contracts to `𝔭` by `comap_polyChain`.

## Generic Noether normalization in finite injective form (section `Normalization`)

Here `D` and `C` are domains in universe `u`, `C` is a `D`-algebra with injective structure map
(`FaithfulSMul D C`) and `C` is of finite type over `D`.

`finite_injective_of_generic` takes `r ≠ 0` in `D` and algebraically independent `z : Fin d → C`
such that for each `c : C` some `rⁿ • c` is integral over `D[z]`. These are the outputs of the
FLT theorem. Let `D'` be a localization of `D` away from `r`, and let `C'` be a localization of
`C` at the image of the powers of `r`, with compatible algebra structures (scalar towers
`D → D' → C'` and `D → C → C'`). The theorem gives a `D'`-algebra map
`ψ : D'[X] →ₐ[D'] C'` (variables `ULift (Fin d)`), sending `Xᵢ` to the image of `zᵢ`, that is
finite and injective.

- Integrality. The map `D[z] ≅ D[X] → D'[X]` (`AlgebraicIndependent.aevalEquiv`, renaming and
  base change of coefficients) followed by `ψ` agrees with `D[z] → C → C'`. So the image in `C'`
  of an element integral over `D[z]` is integral over `D'[X]` (`IsIntegral.map_of_comp_eq`). The
  image of a power of `r` is a unit in `C'` and comes from `D'[X]`, so it can be cancelled
  (`IsIntegral.of_mul_unit`). This shows that the images of elements of `C` are integral, and
  then so is every fraction `c / rᵐ` in `C'`.
- Finiteness. `C'` is of finite type over `C`, since it localizes at a finitely generated
  submonoid. Hence `C'` is of finite type over `D` and over `D'`, and `ψ` is of finite type. An
  integral map of finite type is finite (`RingHom.IsIntegral.to_finite`).
- Injectivity. Use `D'[X]` as a localization of `D[X]` at the powers of `C r`
  (`MvPolynomial.algebraMvPolynomial`). If `ψ p = 0`, write `p · C(rᵗ) = p₀` with `p₀ ∈ D[X]`.
  Then `p₀(z)` becomes zero in `C'`, so `rᵏ · p₀(z) = 0` in `C` for some `k`. The domain `C`
  has `rᵏ ≠ 0` because `D → C` is injective. So `p₀(z) = 0`, and algebraic independence gives
  `p₀ = 0`. The image of `rᵗ` is a unit, so `p = 0`.

`exists_away_finite_injective` states the combined result with the concrete localizations
`Localization.Away r` and `Localization (Algebra.algebraMapSubmonoid C (Submonoid.powers r))`:
there are `r ≠ 0` in `D`, `d : ℕ` and a finite injective
`ψ : (Localization.Away r)[X] →ₐ (Localization (algebraMapSubmonoid C (powers r)))`. It applies
the FLT theorem and then `finite_injective_of_generic`.
