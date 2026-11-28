# Projections of square-integrable functions of fixed type are automorphic forms

Module `Langlands.Global.AdelicSquareIntegrableProjectionAutomorphyProof` proves
`Langlands.Global.SquareIntegrableProjectionAutomorphyStatement` (module
`Langlands.Global.AdelicFiniteProjectionReduction`) as
`Langlands.Global.squareIntegrableProjectionAutomorphy`.

| Declaration | Kind | Source |
| --- | --- | --- |
| `isLeftInvariant_canonicalRationalSubgroup` | theorem | internal |
| `isInfiniteSubgroupFiniteFunction_of_mem` | theorem | internal |
| `squareIntegrableProjectionAutomorphy` | theorem | Harish-Chandra 1966, §8, Theorem 1; Getz–Hahn Corollary 6.2.5; Mœglin–Waldspurger I.2.4–I.2.5 |

All names are in the namespace `Langlands.Global`.

## The statement

For a connected reductive `G` over a number field `F`, a maximal compact `K ≤ G(𝔸)` with
`K_∞ = K.comap (ofInfinite F G)`, a closed matrix embedding `rho`, a type `(J, L, E)` and a smooth
function `φ` on `G(𝔸)`, left invariant under `G(F)` and `A_G`, of type `(J, L, E)`, whose class
`f ∈ L²([G])` is given, the orthogonal projection of `f` onto every closed subspace `V` invariant
under the right regular representation `R` is the class of an automorphic form `ψ` on
`G(F) \ G(𝔸)`, left invariant under `A_G` and of the same type. See the Markdown of
`Langlands.Global.AdelicFiniteProjectionReduction` for the conventions.

## Lemmas

- `isLeftInvariant_canonicalRationalSubgroup` shows that a function left invariant under
  `RestrictionSplitCentre.canonicalSubgroup F G` (`A_G`) and under `rationalSubgroup F G` (`G(F)`)
  is left invariant under `RestrictionSplitCentre.canonicalRationalSubgroup F G` (`A_G G(F)`),
  which is their supremum. The elements fixing the function form a subgroup.
- In `isInfiniteSubgroupFiniteFunction_of_mem`, if every function `k ↦ u(g k)` on `K_∞` lies in a
  finite-dimensional space `E`, then `u` is `K_∞`-finite. Each right translate `u(· k)` is the image
  of evaluation at `k`, restricted to `E`, under the linear map
  `Module.Dual ℂ E → (G(𝔸) → ℂ)`, `ℓ ↦ (g ↦ ℓ(u(g ·)))`, whose range is finite-dimensional.

## Proof of `squareIntegrableProjectionAutomorphy`

Write `Γ = A_G G(F)`, `P` for the orthogonal projection onto `V`, `w = P f`, and `R(h)` for the
integrated action `canonicalL2IntegratedAction` of an integrable `h` (module
`Langlands.Global.AdelicCanonicalL2Smoothing`, which also supplies the other results cited below).

1. *A smooth reproducing kernel.* `φ` is left invariant under `Γ`, `K_∞`-finite
   (`isInfiniteSubgroupFiniteFunction_of_mem` with `E`) and `𝔷`-finite (with `J`). The Library
   theorem `exists_adelicTestFunction_rightConvolution_eq` (Harish-Chandra 1966, §8, Theorem 1)
   gives an adelic test function `β` with `rightConvolution F G β φ = φ`.
2. *Integrated actions on `f`.* For an integrable `k`, `R(k) f` is represented by
   `y ↦ rightConvolution F G k φ (y.out)` (`canonicalL2IntegratedAction_ae_eq` and
   `canonicalL2Smoothing_eq_rightConvolution`). Hence `R(β) f = f`, and, since `P` commutes with
   `R(β)` (`starProjection_canonicalL2IntegratedAction`), `R(β) w = w`.
3. `ψ = canonicalL2Smoothing β w` is smooth
   (`isAdelicSmoothFunction_canonicalL2Smoothing`), left invariant under `Γ`
   (`canonicalL2Smoothing_mul`), hence under `G(F)` and `A_G`, and represents `R(β) w = w`
   (`canonicalL2IntegratedAction_ae_eq`). It has
   moderate growth (`hasModerateGrowthFunction_canonicalL2Smoothing`, the folding estimate of
   Mœglin–Waldspurger I.2.5 (b) with the count of I.2.4 (a)(i)).
4. For `b ∈ L`, `R(b) f = f` because `φ` is right invariant, so
   `R(b) w = P R(b) f = w` (`starProjection_canonicalL2RightAction`). The continuous left
   `Γ`-invariant functions `x ↦ ψ(x b)` and `ψ` represent `R(b) w` and `w`
   (`canonicalL2RightAction_ae_eq`), so they are equal (`eq_of_ae_eq_out`).
5. `Langlands.Analysis.finiteSubspaceInterpolation`
   gives points `k_j ∈ K_∞` and functions `e_j ∈ E` with `u(k) = ∑_j e_j(k) u(k_j)` for every
   `u ∈ E`. Applied to `u = φ(g ·)` this gives `R(k) f = ∑_j e_j(k) R(k_j) f` in `L²([G])`, hence
   `R(k) w = ∑_j e_j(k) R(k_j) w` after applying `P`. Both sides have continuous left
   `Γ`-invariant representatives, so `ψ(x k) = ∑_j e_j(k) ψ(x k_j)` for all `x` and `k`, and
   `k ↦ ψ(g k) = ∑_j ψ(g k_j) e_j` lies in `E`. By `isInfiniteSubgroupFiniteFunction_of_mem`, `ψ`
   is `K_∞`-finite.
6. For `z ∈ J`, the Library theorem `adelicRightConvolutionEnveloping`
   gives an adelic test function `k` with
   `z (rightConvolution β f') = rightConvolution k f'` on every infinite slice, for every
   measurable locally integrable `f'` (this is how derivatives pass under the convolution
   integral, Getz–Hahn, proof of Corollary 6.2.5). With `f' = φ`, the left side is `z φ = 0`, so
   `rightConvolution k φ = 0`, hence `R(k) f = 0` by step 2 and `R(k) w = P R(k) f = 0`. The
   continuous left `Γ`-invariant function `canonicalL2Smoothing k w` represents `R(k) w`, so it is
   zero (`eq_of_ae_eq_out`). With `f'` the pullback of `w`, the slices of `z ψ` are the slices of
   `canonicalL2Smoothing k w`, which vanish. So every `z ∈ J` annihilates every slice of `ψ`, and
   `ψ` is `𝔷`-finite.

Steps 3–6 give `IsAutomorphicFunctionOn F G hsmooth hcalc (rationalSubgroup F G) K_∞ rho ψ`, the
left invariance of `ψ` under `A_G`, its type `(J, L, E)` and `P f =ᵐ ψ ∘ out`. The interpolation
identity in step 5 transports the compact type using only the reproducing kernel for `φ`.

## Sources

- Harish-Chandra, *Discrete series for semisimple Lie groups II*, Acta Math. 116 (1966),
  `harish-chandra-1966-discrete-series-ii` (SHA-256
  `3ad72529bddbfe96e537bc3f49df6aa3223169c2abbe265d858c32c48545f3d9`), §8, Theorem 1, pp.18–19.
- J. R. Getz and H. Hahn, *An introduction to automorphic representations* (2024),
  `getz-hahn-2024-automorphic-representations` (SHA-256
  `a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`), Theorem 6.2.4 and
  Corollary 6.2.5 with its proof, p.160 (PDF p.174).
- C. Mœglin and J.-L. Waldspurger, *Spectral decomposition and Eisenstein series* (1995),
  `moeglin-waldspurger-1995-spectral-decomposition`, chapter file
  `05.2_pp_18_40_Automorphic_forms_growth_constant_terms.pdf` (SHA-256
  `296dcb3e7170bb0c2689cf0c79136a43cd86976df2b4c51f027cf9365f7fe988`), I.2.4, Lemma (a)(i),
  pp.25–26, and I.2.5, Lemma (b), p.27.
- A. Borel and H. Jacquet, *Automorphic forms and automorphic representations* (1979),
  `borel-jacquet-1979-automorphic` (SHA-256
  `3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`), §3.2 and §4.1–4.3,
  pp. 194–195 (PDF pp. 189–190).
