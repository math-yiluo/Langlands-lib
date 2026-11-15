# Real principal series have an infinitesimal character

Lean module: `Langlands.Representation.Archimedean.RealPrincipalSeriesInfinitesimalCharacter`.

## Statement

`Langlands.Archimedean.RealPrincipalSeriesInfinitesimalCharacterStatement`:

```lean
def RealPrincipalSeriesInfinitesimalCharacterStatement : Prop :=
  ∀ (n : ℕ) (χ : ℕ → ℝˣ → ℂ), HasInfinitesimalCharacter (principalSeriesLie ℝ n χ)
```

Fix `n` and a family `χ` of characters of `ℝˣ`. `principalSeries ℝ n χ` is the Library's
smooth principal series of `GL_n(ℝ)`. Its elements are the smooth functions `f` with
`f(diag(a) u g) = principalSeriesCharacter ℝ n χ a · f(g)` for `u` upper unipotent.
`principalSeriesLie ℝ n χ` is the action of `ℂ ⊗_ℝ 𝔤𝔩_n(ℝ)` on its `O(n)`-finite functions,
with `1 ⊗ X` acting by the right derivative `R(X)`. The statement says that this action has an
infinitesimal character (`HasInfinitesimalCharacter`, Library `RealGenericLargeReduction`):
every element of the center of `U(ℂ ⊗_ℝ 𝔤𝔩_n(ℝ))` acts by a scalar. The statement carries no
hypothesis on `n` or `χ`.

The module also proves the statement (`realPrincipalSeriesInfinitesimalCharacter`). It proves
it as a special case of a more general theorem,
`RealPrincipalSeriesInfChar.hasInfinitesimalCharacter_kFiniteLie`. Let `V` be a space of
functions on `GL_n(ℝ)` contained in `principalSeries ℝ n χ` (hypothesis `hVps`). Suppose `V`
consists of smooth functions (`hV`) and is stable under right translation by `O(n)` (`hVK`) and
under right derivatives (`hVX`). Then the derivative action `kFiniteLie V hV hVK hVX` on the
`O(n)`-finite functions of `V` has an infinitesimal character. The corollary
`realStandardLie_hasInfinitesimalCharacter` gives
`HasInfinitesimalCharacter (realStandardLie n ds)` for every list `ds` of real blocks. Here
`V = realStandardModule n ds`, which lies in a principal series by the Library lemma
`realStandardModule_le_principalSeries`.

## Provenance

This is an internal statement, introduced as a prerequisite for
`RealLinkedLanglandsQuotientNotLargeStatement` (Task 7070). The reduction
`realLinkedLanglandsQuotientNotLarge_of_quotientAnnihilator` (module
`RealLinkedQuotientAnnihilator`) takes the corollary
`realStandardLie_hasInfinitesimalCharacter` as its hypothesis `hZ`. Mathematically it is the
classical fact, due to Harish-Chandra, that a principal series representation (and every
subrepresentation of it) has an infinitesimal character. Here it is specialised to `GL_n(ℝ)`
with the Library's normalisation. It is the real counterpart of the Library module
`ComplexPrincipalSeriesInfinitesimalCharacter`, and the proof follows the same outline.

## Proof

Fix `V` as above and let `ev₁ = kFiniteEval V 1` be evaluation at `1` on the `O(n)`-finite
functions of `V`.

1. **Evaluation at `1` is a lowest-weight functional.**
   - `fderiv_upper_mul_eq_zero`: let `f` be in the principal series with `f(g) = 0`, and let
     `U` be upper triangular. Write `U = Δ + N` with `Δ` diagonal and `N` strictly upper
     triangular. The curve `Γ(t) = exp(tΔ) (1 + tN) g` has derivative `U g` at `0`. It equals
     `exp(diag(t U_ii)) · unipotentLine N t · g`, a diagonal unit times an upper unipotent
     element times `g` (Library `RealPrincipalSeriesDuality.unipotentLine`,
     `matrixExpUnit_diagonal`, `hasDerivAt_exp_smul_zero`). So `f` vanishes along `Γ`, and the
     derivative of the smooth extension of `f` at `g` in direction `U g` is `0`.
   - `rightDerivative_apply_one_eq_zero`: the case `g = 1`. If `f(1) = 0` and `X` is upper
     triangular, then `(R(X) f)(1) = 0`.
   - `tmul_mem_scalarSubmodule`: hence `ev₁ ∘ R(X)` vanishes on the kernel of `ev₁`. By the
     Library lemma `ComplexPrincipalSeriesInfChar.exists_eq_smul_of_ker_le` it is a multiple of
     `ev₁`. So every `c ⊗ X` with `X` upper triangular acts on `ev₁` by a scalar.
2. **Weight element and lowering elements.**
   - `weightH = 1 ⊗ D` with `D = diag(0, -1, …, -(n-1))`.
   - `lowering` is the set of elements `c ⊗ r E_pq` with `c ∈ ℂ`, `r ∈ ℝ` and `q < p`, where
     `E_pq` is a matrix unit.
   - `lie_weightH_lowering`: `⁅weightH, y⁆ = -((p - q) • y)` with `p - q > 0`. This uses
     `diagonal_mul_sub_mul_diagonal`: `[diag(d), r E_pq] = (d_p - d_q) r E_pq`.
   - `decSubmodule_eq_top`: every element of `ℂ ⊗_ℝ 𝔤𝔩_n(ℝ)` is a sum of terms
     `c ⊗ r E_pq`. The strictly lower ones lie in `lowering`, and the others act on `ev₁` by
     scalars by step 1.
3. **Central elements act on `ev₁` by scalars.** The Library lemma
   `JacquetCenter.exists_comp_envelopingAction_eq_smul` gives, for central `z`,
   `ev₁ ∘ Z = c · ev₁` with `Z = envelopingAction (kFiniteLie V hV hVK hVX) z`.
4. **From `ev₁` to all of `GL_n(ℝ)`** (`hasInfinitesimalCharacter_kFiniteLie`).
   - `Z` commutes with right translation `ρ(k)` for every `k ∈ O(n)`. This combines the Library
     lemmas `InfinitesimalCharacter.rho_mul_envelopingAction` (with the `(𝔤, K)`-compatibility
     from `isRealGKModule_kFinite`) and `InfinitesimalCharacter.fixesCenter_of_det_ne_zero`
     (central elements are fixed by conjugation by an invertible real matrix).
   - Hence `(Z f)(k) = ev₁(Z ρ(k) f) = c · ev₁(ρ(k) f) = c · f(k)` for all `k ∈ O(n)`.
   - `Z f - c f` lies in the principal series and vanishes on `O(n)`. By the Iwasawa
     decomposition (Library `eq_zero_of_mem_principalSeries_of_eqOn_unitaryCompact`) it is `0`.
     So `Z = c · id`.

`realPrincipalSeriesInfinitesimalCharacter` applies this with `V = principalSeries ℝ n χ`, and
`realStandardLie_hasInfinitesimalCharacter` with `V = realStandardModule n ds`.
