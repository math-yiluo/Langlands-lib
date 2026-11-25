# Complex principal series have an infinitesimal character

Lean module: `Langlands.Representation.Archimedean.ComplexPrincipalSeriesInfinitesimalCharacter`.

## Statement

`Langlands.Archimedean.ComplexPrincipalSeriesInfinitesimalCharacterStatement`:

```lean
def ComplexPrincipalSeriesInfinitesimalCharacterStatement : Prop :=
  ∀ (n : ℕ) (χ : ℕ → ℂˣ → ℂ), HasInfinitesimalCharacter (principalSeriesLie ℂ n χ)
```

Fix `n` and a family `χ` of characters of `ℂˣ`. `principalSeries ℂ n χ` is the Library's
smooth principal series of `GL_n(ℂ)`. Its elements are the smooth functions `f` with
`f(diag(a) u g) = principalSeriesCharacter ℂ n χ a · f(g)` for `u` upper unipotent.
`principalSeriesLie ℂ n χ` is the action of `ℂ ⊗_ℝ 𝔤𝔩_n(ℂ)` on its `U(n)`-finite functions, with
`1 ⊗ X` acting by the right derivative `R(X)`. The statement says that this action has an
infinitesimal character (`HasInfinitesimalCharacter`, Library `RealGenericLargeReduction`):
every element of the center of `U(ℂ ⊗_ℝ 𝔤𝔩_n(ℂ))` acts by a scalar. The statement carries no
hypothesis on `n` or `χ`.

The module also proves the statement (`complexPrincipalSeriesInfinitesimalCharacter`). Its
corollary `complexStandardLie_hasInfinitesimalCharacter` gives
`HasInfinitesimalCharacter (complexStandardLie n ds)` for every list `ds` of complex
characters. It holds by definition, since `complexStandardLie n ds` is
`principalSeriesLie ℂ n (complexPositionCharacter ds)`.

## Provenance

This is an internal statement, introduced as a prerequisite for the non-largeness half
(`ComplexLinkedLanglandsQuotientNotLargeStatement`) of the proof of
`ComplexLargeStandardIrreducibleStatement`. Mathematically it is the
classical fact, due to Harish-Chandra, that a principal series representation has an
infinitesimal character, specialised to `GL_n(ℂ)` with the Library's normalisation.

## Proof

The proof goes through the product presentation. `tensorLieEquiv`
(`ComplexGenericLargeReduction`) is the Lie algebra isomorphism
`ℂ ⊗_ℝ 𝔤𝔩_n(ℂ) ≃ 𝔤𝔩_n(ℂ) × 𝔤𝔩_n(ℂ)`, and `prodAction π = π ∘ tensorLieEquiv⁻¹`. By
`Kostant.hasInfinitesimalCharacter_of_comp` it suffices to treat
`prodAction (principalSeriesLie ℂ n χ)`, an action of `Fin 2 → Matrix (Fin n) (Fin n) ℂ`.

1. **Evaluation at `1` is a lowest-weight functional.** `evalOne χ` is evaluation at `1` on the
   `U(n)`-finite functions.
   - `rightDerivative_apply_one_eq_zero`: if `f` lies in the principal series, `f(1) = 0` and
     `X` is upper triangular, then `(R(X) f)(1) = 0`. Indeed `f` vanishes on the invertible
     upper triangular matrices. The strictly upper triangular part of `X` is handled by the
     Library lemma `LieInvariance.fderiv_strictUpper_mul_eq_zero`. The diagonal part is handled
     by `fderiv_diagonal_eq_zero`, which differentiates along the curve `t ↦ exp(t diag(d))`.
   - With `exists_eq_smul_of_ker_le` (a functional vanishing on `ker ψ` is a multiple of `ψ`),
     every `1 ⊗ X` with `X` upper triangular acts on `evalOne χ` by a scalar
     (`one_tmul_mem_scalarSubmodule`). Via the explicit preimage `tensorInv`, so does every pair
     `Y = (Y₀, Y₁)` of upper triangular matrices (`mem_scalarSubmodule_prod`).
2. **Weight element and lowering elements.**
   - `weightH = (D, D)` with `D = diag(0, -1, …, -(n-1))`.
   - `lowering` is the set of pairs with one component a multiple of a strictly lower
     triangular matrix unit `E_pq` (`q < p`) and the other component `0`.
   - `lie_weightH_lowering`: `⁅weightH, y⁆ = -((p - q) • y)` with `p - q > 0`.
   - `decSubmodule_eq_top`: every element is a sum of matrix units placed in one component.
     The strictly lower ones lie in `lowering`, the others act on `evalOne χ` by scalars.
3. **Central elements act on `evalOne χ` by scalars.** The general lemma
   `JacquetCenter.exists_comp_envelopingAction_eq_smul` gives, for central `z`,
   `evalOne χ ∘ Z = c · evalOne χ` with `Z = envelopingAction (prodAction …) z`.
4. **From `evalOne` to all of `G`.**
   - `Z` commutes with right translation `ρ(k)` by every `k ∈ U(n)`. This combines the Library
     lemmas `rho_mul_envelopingAction_prod` and `pairFixesCenter_of_det_ne_zero` (central
     elements are fixed by `Ad(k, k̄)`).
   - Hence `(Z f)(k) = evalOne(Z ρ(k) f) = c · evalOne(ρ(k) f) = c · f(k)` for all `k ∈ U(n)`.
   - `Z f - c f` lies in the principal series and vanishes on `U(n)`. By the Iwasawa
     decomposition (Library `ComplexDuality.eq_zero_of_mem_principalSeries_of_eqOn`) it is `0`.
     So `Z = c · id`.
