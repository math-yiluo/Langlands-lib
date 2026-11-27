# Splitting an intertwining integral along an exponent decomposition

Module `Langlands.Global.CuspidalTestExpansion.PieceExpansion`
(namespace `Langlands.Global.StandardParabolicFamily`).

## Statement

`intertwiningIntegral_exponentExpansion`: let `n`, `c`, `π`, `K` be as in
`exists_offset_hasPolynomialOrbit_intertwiningIntegral` and let `offset` satisfy the
conclusion of that theorem (hypothesis `hoffset`). Let `f` be continuous and left invariant
under `U_{I₁}(𝔸)`, with intertwining integrand at parameter `λ` integrable at every argument,
and let `f = ∑_{ν ∈ s} comp ν` be a finite sum of continuous, `U_{I₁}(𝔸)`-invariant functions
such that `comp ν` has unnormalized exponent `ν` along `I₁` with polynomial degree at most `k`
(`HasPolynomialOrbit I₁ ν k (comp ν)`, one `k` for all `ν ∈ s`). Then, writing `Int h` for the
intertwining integral `hK.intertwiningIntegral (fam.iU I₁) (fam.iU J ≫ fam.p J) n h λ`:

- `Int f = ∑_{ν ∈ s} Int (comp ν)`;
- for every `ν ∈ s`, `Int (comp ν)` has unnormalized exponent
  `weylParameter (fam.l I₁) c π (ν + λ) + offset` along `J` with polynomial degree at most `k`,
  and lies in `translateSpan J (Int f)`.

## Proof

Each `comp ν` lies in `translateSpan I₁ f` (`mem_translateSpan_of_sum`), so its intertwining
integrand is integrable at every argument (`integrable_intertwiningIntegrand_of_mem_translateSpan`)
and so are those of its positive translates. The integrand of `f` is the finite sum of the
integrands of the `comp ν`, so `integral_finsetSum` gives the first claim. The exponent comes
from `hoffset`, and the span statement from `intertwiningIntegral_mem_translateSpan`.
