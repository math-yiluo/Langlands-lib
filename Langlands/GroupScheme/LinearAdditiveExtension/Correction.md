# Correcting a crossed homomorphism into the closed additive subgroup

Module `Langlands.GroupScheme.LinearAdditiveExtension.Correction`, namespace
`Langlands.GroupScheme.LinearAdditiveExtension`.

The setting is that of `CrossedHom`, over an algebraically closed field `k`. The input
`c' : E ⟶ 𝔾ₐ` satisfies two pointwise identities on every test scheme:

- `hc₁`: `c'(g h) = c'(g) + χ(q g) c'(h)`;
- `hc₂`: `c'(ι u) = a(u)`.

`exists_corrected` finds `c''` with the same two properties whose values all lie in the range
of the closed subgroup `a`. This is the step "`Ext⁰(φ)` is surjective" in the proof of Milne,
*Algebraic Groups* (2022), Theorem 15.34(d). There, `U = Ker(φ)` for an additive `φ`
(Exercise 14-3), and crossed homomorphisms of `D` lift along `φ`. The Lean proof is internal; it
uses the closed polynomial `f` of `ClosedAdditivePolynomial` in place of `φ`.

## Helpers

- `base` is `Spec k` over itself. `toBase` is the unique map to it, with `comp_toBase`, and
  `isAffineHom_base`.
- `pow_comp'`: precomposition commutes with powers of points of `D`.
- `cd_polyEndo`: the published endomorphism `AdditiveGroupQuotient.polyEndo f` evaluates `f`
  on coordinates.
- `structureMap_base_surjective` and `structureMap_toBase`: functions on the base are constants
  from `k`, and they pull back to the structure map of every test scheme.
- `weight_stable`: the hypothesis `hlin` makes the range of `a` stable under the linear action
  of `D` through `χ`.

## The proof of `exists_corrected`

Let `f = closedPolynomial a`.

- If `f = 0`, every point lies in the range of `a`, by `mem_range_iff_eval`, and `c'' = c'`.
- Otherwise let `N` be the degree of `f`. The function `f ∘ c'` is invariant under right
  translation by kernel points. The reason: `f` is additive (`eval₂_add`), and
  `χ(q g) a(u) = a(b(q g, u))` lies in the range, where `f` vanishes. So it descends to
  `hD : D ⟶ 𝔾ₐ` with `q ≫ hD = c' ≫ polyEndo f`.
- `hD` is a crossed homomorphism for `χ^N`: `hD(z z') = hD(z) + χ(z)^N hD(z')`. This is
  checked after cancelling the epimorphism `q ⊗ q`
  (`FpqcHomDescent.epi_tensorHom`). It uses additivity of `f` and the scaling identity
  `eval₂_charValue_mul`.
- Averaging over `D` (`DiagonalizableAverage`) gives a constant `mu : base ⟶ 𝔾ₐ` with
  `mu = hD(z) + χ(z)^N mu` for every point `z` of `D`. That is, `hD = mu (1 − χ^N)`. The proof
  averages the crossed identity, written for `z' z = z z'`, in the variable `z'`. It uses
  `average_translate`, `average_mul`, `average_snd` and `average_weightAction`.
- `mu` is a constant `m₀ ∈ k`. Since `k` is algebraically closed and `f` has positive degree,
  `f(r₀) = m₀` for some `r₀ ∈ k` (`IsAlgClosed.exists_root`).
- `c'' = c' + r₀ (χ ∘ q − 1)`, written with the action `VectorGroup.weightAction χ` and the
  constant point with coordinate `r₀`. It satisfies `hc₁` and `hc₂`, and
  `f(c''(g)) = hD(q g) + (χ(q g)^N − 1) f(r₀) = 0`. By the membership criterion, every value of
  `c''` lies in the range of `a`.
