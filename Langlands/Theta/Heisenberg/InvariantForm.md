# Invariant sesquilinear forms on the Schrödinger model

**GKT §1.3.1** (Theorem 1.31: the Heisenberg representation is unitarizable, p. 36) and
**Appendix A**, Lemma A.16 (p. 602: the unitary structure of an irreducible admissible unitary
representation is unique up to a scalar), proved for the Schrödinger model without Schur's lemma;
it fixes the measures of GKT Proposition 1.21 (p. 30) and Proposition 2.13 (p. 55), "the unique
measure that makes the operator unitary".

The module `Langlands.Theta.Heisenberg.InvariantForm` proves that every sesquilinear form on the
Schrödinger model `S(X)` invariant under the Heisenberg group is a multiple of the `L²` inner
product, and deduces that a non-zero operator intertwining the model with a twist of itself is a
positive multiple of a unitary operator.

## Content

Let `F` be a nonarchimedean local field with `2 ≠ 0`, `β : X →ₗ[F] Y →ₗ[F] F` a pairing of
finite-dimensional spaces with their module topologies, `ψ` a continuous character, `μ` a Haar
measure on `X`, and `σ = schrodingerSB hψ hβ`.

- `IsSchrodingerInvariant hψ hβ B`: `B(σ(h) φ, σ(h) φ') = B(φ, φ')` for all `h`;
  `isSchrodingerInvariant_schwartzBruhatInner`: the `L²` form is invariant.
- `exists_eq_mul_schwartzBruhatInner` (for a perfect pairing and `ψ ≠ 1`): an invariant `B` is
  `c ⟨,⟩_μ` for some `c ∈ ℂ`.
- `exists_pos_schwartzBruhatInner_map`: a non-zero linear `T` of `S(X)` with
  `T ∘ σ(h) = σ(a h) ∘ T` for a map `a` of the Heisenberg group satisfies
  `⟨T φ, T φ'⟩ = C ⟨φ, φ'⟩` with `C > 0` (apply the previous theorem to `⟨T ·, T ·⟩`, positivity on
  a vector with `T φ ≠ 0`).
- `schwartzBruhatInner_self_eq_integral`, `integral_norm_sq_pos`: `⟨f, f⟩ = ∫ ‖f‖²`, positive for
  `f ≠ 0` (a measure positive on open sets).

**Proof of the first theorem.** For a pair of compact open subgroups `L ⊆ X`, `M = L^⊥ ⊆ Y` each
the orthogonal of the other (`SchrodingerIrreducible.Internal.LatticePair`), and the indicators
`1_{z+L} = σ(−z, 0) 1_L` (`InvariantForm.Internal.cosetIndicator`):

1. `σ(0, y)`, `y ∈ M`, multiplies `1_{z+L}` by `ψ(β(z, y))`
   (`InvariantForm.Internal.schrodingerSB_cosetIndicator`);
2. so `B(1_{z+L}, 1_{z'+L}) = ψ(β(z' − z, y)) B(1_{z+L}, 1_{z'+L})`, and if `z' − z ∉ L = M^⊥` there
   is `y ∈ M` with `ψ(β(z' − z, y)) ≠ 1`: `B` vanishes on different cosets
   (`invariant_cosetIndicator_of_sub_notMem`);
3. `B(1_{z+L}, 1_{z+L}) = B(1_L, 1_L)` by invariance under translations
   (`invariant_cosetIndicator_self`);
4. an `L`-invariant `φ` vanishing off a compact set is `∑ φ(c) 1_{c+L}` over finitely many cosets
   (`eq_sum_cosetIndicator`, from `SchrodingerIrreducible.Internal.eq_sum_translates`), hence
   `B(φ, φ') = (∑_c conj φ(c) φ'(c)) B(1_L, 1_L)` (`invariant_eq_sum`).

The same holds for `⟨,⟩_μ`; comparing with a fixed `1_{L₀}` and choosing `L ⊆ L₀` small enough for
`φ`, `φ'` gives `B = (B(1_{L₀}, 1_{L₀}) / ⟨1_{L₀}, 1_{L₀}⟩) ⟨,⟩_μ`.

## Declarations

- `IsSchrodingerInvariant`.
- Internal (`Langlands.HeisenbergGroup.InvariantForm.Internal`): `cosetIndicator`,
  `cosetIndicator_apply`, `schrodingerSB_cosetIndicator`, `invariant_cosetIndicator_of_sub_notMem`,
  `invariant_cosetIndicator_self`, `eq_sum_cosetIndicator`, `invariant_eq_sum`.
- `schwartzBruhatInner_self_eq_integral`, `integral_norm_sq_pos`.
- `isSchrodingerInvariant_schwartzBruhatInner`, `exists_eq_mul_schwartzBruhatInner`,
  `exists_pos_schwartzBruhatInner_map`.

All in the name space `Langlands.HeisenbergGroup`.

## Dependencies

`Langlands.Theta.Heisenberg.SchrodingerUnitary` (`schwartzBruhatInner`, `schrodingerSB_inner`),
`Langlands.Theta.Heisenberg.SchrodingerIrreducible` (`LatticePair`, `eq_sum_translates`,
`norm_addChar_eq_one`), `Langlands.HarmonicAnalysis.Bicharacter.Fourier`
(`exists_nhds_add_eq_of_mem_schwartzBruhatSubmodule`, `indicator_one_mem_schwartzBruhatSubmodule`,
`indicator_invariant`).
