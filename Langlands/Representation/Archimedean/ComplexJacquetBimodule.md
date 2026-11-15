# One-sided nonvanishing for Harish-Chandra bimodules of `𝔤𝔩_n(ℂ)`

Module: `Langlands.Representation.Archimedean.ComplexJacquetBimodule`. The module contains one
Prop-valued definition and proves nothing.

## Statement

`Langlands.Archimedean.ComplexJacquetBimoduleStatement.{uV}` says: for every `n`, every complex
vector space `V : Type uV` and every pair of Lie algebra homomorphisms
`ℓ r : 𝔤𝔩_n(ℂ) → End_ℂ(V)` such that

1. `ℓ` and `r` commute: `ℓ(X) r(Y) = r(Y) ℓ(X)`;
2. `E ⊆ V` is a finite-dimensional subspace with `E ≠ 0`;
3. `E` is stable under `κ(Y) = ℓ(Y) - r(Yᵀ)` for every `Y ∈ 𝔤𝔩_n(ℂ)`;
4. `E` is spanned by vectors `e ∈ E` with `κ(E_pp) e = m_p e` for all `p`, for some integers
   `m_p` (integral weights of `κ` on `E`);
5. `V` is the smallest `ℓ`-stable subspace containing `E`;
6. `ℓ` has an infinitesimal character: every central element of `U(𝔤𝔩_n(ℂ))` acts through the
   extension of `ℓ` by a scalar (`HasInfinitesimalCharacter ℓ` from
   `Langlands.Representation.Archimedean.RealGenericLargeReduction`);

the span of the vectors `ℓ(E_pq) v`, `p < q`, `v ∈ V`, is not all of `V`.

## Role and provenance

This is an internal, algebraic reformulation used for Task 7065 (Casselman's nonvanishing
`V ≠ 𝔫V` for irreducible admissible `(𝔤𝔩_n(ℂ), U(n))`-modules, Wallach 1979, 4.14(1)). For such
a module `(ρ, π)`, take `ℓ(Y) = π(Y, 0)` and `r(Y) = π(0, Y)` under the Library identification
`ℂ ⊗_ℝ 𝔤𝔩_n(ℂ) ≅ 𝔤𝔩_n(ℂ) × 𝔤𝔩_n(ℂ)`, `z ⊗ X ↦ (zX, z X̄)`. For skew-Hermitian `Y` one has
`X̄ = -Xᵀ`, so `κ(Y) = π(1 ⊗ Y)` is the differentiated `U(n)`-action, extended complex
linearly. `E` is the `U(n)`-span of a nonzero vector; conditions 3–6 come from the
`(𝔤, K)`-module axioms, the integrality of the weights of the compact torus, irreducibility and
the infinitesimal character. The conclusion is then the Library's
`ComplexJacquetOneSidedStatement` (module `ComplexJacquetOneSided`), which implies the target
`ComplexJacquetModuleFiniteStatement` by `complexJacquetModuleFinite_of_oneSided`.

The algebraic statement itself is the special case, for the Harish-Chandra bimodule `X = V`
with left action `r` and right action `x · Y = ℓ(Yᵀ) x`, of Bernstein–Gelfand's theorem that
`X ↦ X ⊗_U M(λ)` is faithful on Harish-Chandra bimodules with right central character `χ_λ`,
`λ` dominant (J. Bernstein, S. Gelfand, *Tensor products of finite and infinite dimensional
representations of semisimple Lie algebras*, Compositio Math. 41 (1980), Theorem 5.9 and its
proof 5.10): `X ⊗_U M⁻(λ) = V / (ℓ(𝔫) V + Σ_p (ℓ(E_pp) - λ_p) V) ≠ 0`. Bernstein and Gelfand do
not state this specific formulation; it is ours.

## Planned use

Two reductions are planned in Task 7065: `ComplexJacquetBimoduleStatement` implies
`ComplexJacquetOneSidedStatement` (the `(𝔤, K)`-module bridge described above), and
`BernsteinGelfandInputsStatement` (module `LowerVerma`) implies `ComplexJacquetBimoduleStatement`
(the argument of Bernstein–Gelfand 5.10 with `X = V`). Neither is part of this module.
