# The Bernstein–Gelfand chase at a prescribed weight

Module: `Langlands.Representation.Archimedean.BGChaseWeighted`, namespace
`Langlands.Archimedean.BGChase`. Everything here is proved. It is a variant of
`complexJacquetBimodule_of_inputs` (module `BGChaseConclusion`, which formalizes
Bernstein–Gelfand 1980, proof of Theorem 5.9 in 5.10). That theorem obtains the weight `λ` of the
lower Verma module `M = M⁻(λ)` from `CentralCharacterStatement`. Here `λ` is given as a hypothesis,
and the chase uses the extra generators `x · (E_pp - λ_p)`, which `c_gen` also kills. This is
internal content derived from that proof; the literature has no separate statement of it. It is
used for the spherical tempered core, where `λ` is the exponent of the evaluation-at-`1`
functional.

`U = U(𝔤𝔩_n(ℂ))`; `E_pq = Matrix.single p q 1`, with image `unitU n p q` in `U`; `gen n λ` is the
generator of `M⁻(λ)`.

## Definitions

- `wtSpan ℓ λ`: for a Lie algebra action `ℓ` of `𝔤𝔩_n(ℂ)` on `V` and `λ : Fin n → ℂ`, the span of
  the vectors `ℓ(E_pq) v` (`p < q`, `v ∈ V`) and `ℓ(E_pp) v - λ_p v` (`v ∈ V`).

## Lemmas on the bimodule data

For `D : BData n V` (module `BGChaseSetup`):

- `cM_gen_rmul_diag`: `c_gen(x · (E_pp - λ_p)) = 0`, because `(E_pp - λ_p) · gen = 0` in `M⁻(λ)`
  (`unitU_smul_gen_diag`) and `c_m(x · u) = c_{u·m}(x)` (`cM_rmulE`).
- `ℓ_pmap_sub`: `ℓ(E_pp) p(x) - λ_p p(x) = p(x · (E_pp - λ_p))`, from `p(x · u) = ρ(u) p(x)`
  (`pmap_rmul`), `ρ(E_pp) = ℓ(E_ppᵀ) = ℓ(E_pp)`, and `ρ(c) = c` for scalars.
- `exists_ker_cM_gen_wt`: suppose `E` generates `V` under `ℓ` and `wtSpan ℓ λ = V`. Then for each
  `e ∈ E` some `k ∈ ker p` has `c_gen(k) = e ⊗ gen`. Proof: `p` is onto (`range_pmap`), so
  `V = p(T)` for `T` the span of the `x · E_ab` (`b < a`) and the `x · (E_pp - λ_p)`. Write
  `e = p(y)`, `y ∈ T`. Then `c_gen(y) = 0` by `cM_gen_rmul_of_lt` and `cM_gen_rmul_diag`, and
  `k = e ⊗ 1 - y` works.

## The theorem

`wtSpan_ne_top`. Hypotheses:

- `ℓ`, `r`: commuting Lie algebra actions of `𝔤𝔩_n(ℂ)` on `V`;
- `E ⊆ V`: nonzero and finite-dimensional, stable under `ℓ(Y) - r(Yᵀ)`, spanned by vectors `e` with
  `ℓ(E_pp) e - r(E_pp) e = m_p e` for integers `m_p`, and generating `V` under `ℓ`;
- `λ`: `Z`-extremal (`IsZExtremal n λ`);
- `χ`: an algebra character of the center with `ρ(z) = χ(z)` on `V` (`rhoR ℓ z`, i.e. `Λ_ℓ(zᵗ)`)
  and `z · gen λ = χ(z) gen λ`.

Conclusion: `wtSpan ℓ λ ≠ V`.

Proof. Suppose `wtSpan ℓ λ = V`, and set `D = ⟨ℓ, r, hcomm, E, hstable⟩`. Then `κ` on `E` has
integral weights (`intSpan_kE`), and `ker p` is stable under right multiplication and `κ ⊗ ad`
(`rmul_mem_ker`, `adP_mem_ker`). So `exists_mem_cM_eq` from `BGChaseConclusion` applies, with
`exists_ker_cM_gen_wt` and the proved inputs `VermaPBW.lowerVermaWeight`,
`VermaPBW.lowerVermaDuflo`, `VermaKostant.lowerVermaKostant`, `VermaPBW.lowerVermaHomBound` and
`VermaPBW.lowerVermaProjective`. It gives for each `e ∈ E` some `h ∈ ker p` with `c_m(h) = e ⊗ m`
for all `m ∈ M`. Then `c_m(h - e ⊗ 1) = 0` for all `m`, and `pmap_eq_zero_of_cM` gives
`0 = p(h - e ⊗ 1) = -e`. So `E = 0`, a contradiction.
