# Local `L²` bounds for the archimedean derivatives of `K_∞`- and `𝔷`-finite functions

Module `Langlands.Global.AdelicLocalL2DerivativeBoundStatement` states
`Langlands.Global.AdelicLocalL2DerivativeBoundStatement`. It does not prove it; the module
`Langlands.Global.AdelicLocalL2DerivativeBoundProof` proves it (`adelicLocalL2DerivativeBound`).

| Declaration | Kind | Source |
| --- | --- | --- |
| `AdelicLocalL2DerivativeBoundStatement` | statement | derived from Harish-Chandra 1966, §8, Theorem 1 (adelic form: Mœglin–Waldspurger I.2.17, Lemma), by differentiation of the smooth kernel and the Cauchy–Schwarz inequality |

## Statement

The hypotheses are those of `AdelicReproducingKernelStatement` (module
`Langlands.Global.AdelicReproducingKernelStatement`), in the same order. Let `F : Type` be a
number field and `G` an affine group scheme over `F`, locally of finite type and connected
reductive (`IsConnectedReductive G`). Let `K` be a maximal compact subgroup of
`G(𝔸) = AdelicGroupPoints F G` (`IsMaximalCompactSubgroup F G K`) and
`K_∞ = K.comap (ofInfinite F G)` its archimedean part. Fix the smooth atlas
`hsmooth : SmoothOfRelativeDimension d G.X.hom` and the commutator premise `hcalc` that define the
tangent directions `smoothModel F d` of `G(F_∞)`, the enveloping algebra of `G(F_∞)` and its
centre `𝔷`. Let `Φ : G(𝔸) → ℂ` be

1. left invariant under the rational points `G(F)` (`IsLeftInvariantUnder F G (rationalSubgroup F G)`);
2. smooth (`IsAdelicSmoothFunction`: continuous, with plot-smooth archimedean slices, and right
   invariant under an open subgroup of `G(𝔸_f)`);
3. `K_∞`-finite (`IsInfiniteSubgroupFiniteFunction`);
4. `𝔷`-finite (`IsCenterFiniteFunction`).

Then for every word `D : List (smoothModel F d)` there are a compact set `S ⊆ G(𝔸)` and a
constant `C : ℝ≥0` such that

`‖D Φ(g)‖ₑ² ≤ C · ∫⁻ s in S, ‖Φ(g s)‖ₑ² ∂(Measure.haar)` for every `g ∈ G(𝔸)`.

Here `D Φ = adelicIteratedDirectionalValue hsmooth D Φ` (module
`Langlands.Global.AdelicMaximalUnipotentDecay`): for `D = [X₁, …, X_r]` it is
`R(X₁) R(X₂) ⋯ R(X_r) Φ`, where `R(X) f (x) = adelicDirectionalValue hsmooth X f x` is the
derivative at `1` in the direction `X` of `t ↦ f(x · t)`, `t ∈ G(F_∞)`. The empty word gives `Φ`
itself. The integral is the lower Lebesgue integral of the extended nonnegative function
`s ↦ ‖Φ(g s)‖ₑ²` over `S` for the Haar measure `Measure.haar` of `G(𝔸)`. The set `S` and the
constant `C` depend on `Φ` and `D`, not on `g`. No growth condition on `Φ` is assumed.

## Sources

- Harish-Chandra, *Discrete series for semisimple Lie groups II*, Acta Math. 116 (1966) 1–111,
  registered as `harish-chandra-1966-discrete-series-ii`, file SHA-256
  `3ad72529bddbfe96e537bc3f49df6aa3223169c2abbe265d858c32c48545f3d9`, §8, Theorem 1 and its
  proof, printed pp. 18–19: a smooth function `f` on a connected real reductive group whose
  transforms under the centre of the enveloping algebra and the Lie algebra of the maximal compact
  subgroup span a finite-dimensional space satisfies `f * α = f` for a smooth compactly supported
  `α`; footnote (1) on p. 18 records that no condition on `f` at infinity is needed.
- C. Mœglin and J.-L. Waldspurger, *Spectral decomposition and Eisenstein series*, Cambridge
  University Press 1995, registered as `moeglin-waldspurger-1995-spectral-decomposition`, chapter
  file `05.2_pp_18_40_Automorphic_forms_growth_constant_terms.pdf`, SHA-256
  `296dcb3e7170bb0c2689cf0c79136a43cd86976df2b4c51f027cf9365f7fe988`: I.2.5 (right convolution
  `δ(f)φ(g) = ∫ f(h) φ(gh) dh`, printed pp. 26–27) and I.2.17, Lemma (printed p. 38), the adelic
  form of Harish-Chandra's theorem with a smooth compactly supported kernel on `G(𝔸)`.
- For comparison only (not the source of the statement): J. Bernstein, *On the support of
  Plancherel measure*, J. Geom. Phys. 5 (1988) 663–710, registered as
  `bernstein-1988-support-plancherel`, file SHA-256
  `4d96d9b76127df990379dac18e578d613e1bed6c049ab8604f006a837925ea63`, Key Lemma of §3.4,
  printed p. 686 (PDF p. 24): for a function `f` fixed by a regular subgroup and `k > dim 𝔤`,
  `|f(x)|² ≤ C ∫_{Bx} Q(f) dm_X`, where `Q(f)` is the sum of the squares of the derivatives of
  `f` of degree at most `k`. This is a Sobolev estimate, proved by transferring a coordinate
  Sobolev inequality (3.3 (c)).

## Provenance (derived)

The statement follows from Harish-Chandra's smooth reproducing kernel by differentiating under
the integral and applying the Cauchy–Schwarz inequality. This derivation is explanatory and not
proved in this module.

- As in the Markdown page of `AdelicReproducingKernelStatement`, Harish-Chandra's theorem gives a
  smooth compactly supported `α` on `G(F_∞)` reproducing every archimedean slice of `Φ`, and with
  an open compact subgroup `L ⊆ G(𝔸_f)` fixing `Φ` the function `A(a) = c α(a_∞⁻¹) 1_L(a_f)`
  satisfies `Φ(g) = ∫ Φ(g a) A(a) da` for every `g`. The function `A` is smooth in the
  archimedean variable, locally constant in the finite variable and supported in a compact set
  `S`.
- Write `Φ(g x) = ∫ Φ(g a) A(x⁻¹ a) da` (left invariance of Haar measure). For a tangent
  direction `X`, differentiating at `x = 1` along `t ↦ exp(tX)` moves the derivative onto the
  kernel: `R(X)Φ(g) = ∫ Φ(g a) A_X(a) da`, where `A_X` is a derivative of `A` under left
  translation, continuous and supported in `S`. Iterating, every word `D` gives a continuous
  `A_D` supported in `S` with `D Φ(g) = ∫_S Φ(g a) A_D(a) da`.
- The Cauchy–Schwarz inequality gives `|D Φ(g)|² ≤ ‖A_D‖²_{L²} ∫_S |Φ(g a)|² da`, which is the
  statement with `C = ‖A_D‖²_{L²}`.

The same estimate follows without a smooth kernel from the elliptic equation satisfied by the
archimedean slices: a polynomial in Harish-Chandra's elliptic element `ω + 2ω_K` annihilates `Φ`,
left translation preserves the space of its solutions, and interior elliptic estimates bound all
derivatives of a solution at the identity by its `L²` norm on a compact neighbourhood. The module
`Langlands.Global.AdelicLocalL2DerivativeBoundProof` follows this route.

The statement is related to, and different from, the estimate used by Bernstein's Key Lemma and
by Delorme's proof of Proposition 3.5 (Delorme 2023, p. 12). There `|f(x)|²` is bounded by the
local integral of `Q(f)`, a sum of squares of derivatives of `f` (a Sobolev estimate), and the
resulting bound is applied to a function whose derivatives are all weighted square integrable.
Here every derivative `D Φ(g)` is bounded by the local `L²` mass of `Φ` itself, so only `Φ` needs
to be weighted square integrable when the bound is folded onto `[G]`, as in
`logSquareIntegrableSiegelDerivativeBounds_of_reduction`.
