# Fixed-slice absolute convergence and the first Section 4.6 unfolding

Module `Langlands.Representation.RankinSelberg.TwoBlockFixedSliceUnfoldingStatement`.
Declaration `Langlands.RankinSelberg.TwoBlockFixedSliceUnfoldingStatement.{uF,uV,uW}`.

Authors: Worker 778 (Lean and Markdown) and Worker 1175 (independent reading
of JPSS printed pages 409–412 and the errata search).

This module defines one closed proposition and proves nothing. The proposition
is the actual analytic content of the first unfolding in JPSS (1983),
Section 4.6, printed pages 411–412. It applies to the published integrand on
the published quotient `H \ GL_(t+1)` with the fixed project measures. For all
real twist parameters above one bound it states measurability, absolute
fiber integrability, absolute integrability on each determinant slice, the
normalized restricted Bochner identity between the outer integrals over
`N \ G` and `H \ G`, and the representative formula for the radical average.
The test representation ranges over every smooth representation. This is a
derived strengthening of the source, explained below.

## Source

H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika, *Rankin–Selberg
convolutions*, American Journal of Mathematics 105 (1983), 367–464. Source ID
`jpss-1983-rankin-selberg`, file
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
SHA-256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
The PDF has no text layer on these pages. Printed pages 410–412 (one-based PDF
pages 45–47) were read from rendered images. No erratum for this source was
found in the literature index, the Library notes or the project notes.

- Pages 410–411. The blocks are `σ_1 = τ_1 ⊗ α^(-u)` and `σ_2 = τ_2 ⊗ α^u` with
  `α = |det|`. The function `W'` is defined by the Jacquet integral (2) of a
  section `f` of `Ind(G_t, Q; σ_1, σ_2)`. The source reduces its convergence for
  `u ≫ 0` to "a special case of a well-known result". Substituting `W'` into (4.2.1) gives
  equation (4):
  `Ψ^m(W, W'; Φ) = ∫_(N\G^m) Φ(ηg) W(g) ∫_(Ū_Q) f[(1 x; 0 1) g; e, e] θ((1 x; 0 1)) dx`.
- Page 412. Using "`Φ(η_r v g) = Φ(g)` for `v ∈ Ū_Q`" (printed so;
  `Φ(η_r v g) = Φ(η_r g)` is meant), the source "formally" obtains the first integral `∫_(N_(t_1,t_2) \ G_r^m) W(g) f[g; e, e] Φ(ηg) dg`.
  Display (5) defines `N_(t_1,t_2)` as the matrices `diag(n_1, n_2)` with
  `n_i ∈ N_(t_i)`. The source then writes: "It is easy to see (c.f. (4.2)) that
  the function `W(g)Φ(η_r g)` on `G_r^m` is compactly supported modulo `N_r`.
  Thus the integral in (4) is absolutely convergent, and our step is
  justified."

This statement covers equation (4), the first integral on page 412, and the
justification sentence. Display (6), formula (7) and Section 4.7 are not part
of it.

| JPSS | Here |
| --- | --- |
| block ranks `t_1`, `t_2` | `m 0 + 1`, `m 1 + 1` |
| total rank `r = t = t_1 + t_2` | `t + 1`, with `h : ∑ i, (m i + 1) = t + 1` |
| `G_r`, `N_r` | `G = GeneralLinear (t + 1) F.Carrier`, `N = upperUnipotent (t + 1) F.Carrier` |
| `N_(t_1,t_2)`, display (5) | `H = TwoBlockUnipotentQuotient.blockUnipotent h F.Carrier` |
| `N \ G`, `N_(t_1,t_2) \ G` | `NQ = LeftUnipotentQuotient t F.Carrier`, `HQ = BlockQuotient h F.Carrier` |
| `G_r^m = {g : |det g| = q^(-m)}`, source index `m` | determinant slice of index `k : ℤ` |
| `σ_1, σ_2` | `twoBlockOppositeTwistBlocks F m τ u`, exponents `(-u, +u)` |
| `f`, a section of (4.6.1) | `f : TwoBlockJacquet.Sections F h (twoBlockOppositeTwistBlocks F m τ u)` |
| evaluation of `ψ̄`-Whittaker functions at `e` | `fun i => twoBlockOppositeTwistFunctional F m ψ τ u i (ell i)` |
| `W'(g)`, (2) of Section 4.6 | `TwoBlockJacquet.jacquetFunction ψ (fun i => (ell i).val) μR f g` |
| `W ∈ W(π; ψ)` | `Wtest : (coefficientModel π ℓ).toSubmodule` |
| `Φ(ηg)`, `η = (0, …, 0, 1)` | `Φ (lastRow g)` |
| `dx` on `Ū_Q ≅ M(t_1 × t_2)` | `μR = rectangularMeasure ν.val (m 0 + 1) (m 1 + 1)` |
| `W(g) f[g; e, e] Φ(ηg)` on `N_(t_1,t_2) \ G` | `E = TwoBlockUnfolding.integrand …` |
| inner `x`-integral in (4), times `Φ(ηg) W(g)` | `A = radicalAverage F h μR E` |

## The complete statement

The proposition quantifies and binds the following, in this order.

1. Every prime `p` (through `[Fact p.Prime]`) and every canonical field
   `F : PadicField.{uF} p`. With `T := F.canonicalTopologicalData`, the
   statement installs `T.topology`, `T.valuativeRel`, `T.localField`,
   `T.fieldT2`, `T.secondCountableTopology`, the Borel measurable space on
   `F.Carrier` and its `BorelSpace` instance.
2. Every `ψ : UnitaryAdditiveCharacter F.Carrier`. The structure includes
   continuity and nontriviality. Every supplied
   `ν : LocalFactor.PadicAbelian.SelfDualHaar T ψ`. Every `t : ℕ`,
   `m : Fin 2 → ℕ` and `h : ∑ i, (m i + 1) = t + 1`. Both blocks have positive
   rank `m i + 1`; rank one (`m i = 0`) is included.
3. The general linear topology `T.generalLinearTopologicalGroup (t + 1)` and
   the abbreviations `G`, `N`, `H`, `NQ`, `HQ` of the table above, and the
   rectangle `R = Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier`. The groups
   `G`, `N`, `H`, each block unipotent group and the quotients `NQ`, `HQ`
   carry their Borel measurable spaces and `BorelSpace` instances. Each block
   unipotent group also gets second countability from the published
   `generalLinearSecondCountableTopology` through the subtype embedding. The
   dependent product `BlockUnipotents m F.Carrier` and the rectangle `R`
   keep their actual product measurable spaces; their `BorelSpace` instances
   are inferred. This instance block is copied from the published
   `TwoBlockUnipotentQuotientIntegrationStatement`.
4. The measures, all fixed before any representation data:

   ```text
   μG = generalLinearHaar F.Carrier t
   μN = unipotentHaar F.Carrier t
   μH = Measure.map (blockUnipotentEquiv h F.Carrier)
          (Measure.pi (fun i : Fin 2 => unipotentHaar F.Carrier (m i)))
   μR = rectangularMeasure ν.val (m 0 + 1) (m 1 + 1)
   O  = (ValuativeRel.valuation F.Carrier).integer
   c  = μR {x | ∀ a b, x a b ∈ O} : ℝ≥0∞
   ```

5. The proposition then asserts `0 < c`, `c < ⊤`, and the existence of proofs
   `hN : Measure.IsMulRightInvariant μN` and
   `hH : Measure.IsMulRightInvariant μH`. These certificates are installed as
   instances, because `QuotientIntegration.IsCompatible` uses right
   invariance to define its orbital average. With them it asserts
   `∃ νN : Measure NQ, IsCompatible N μG μN νN` and
   `∃ νH : Measure HQ, IsCompatible H μG μH νH`.
6. Still inside this conjunction: for every family of block carriers
   `W : Fin 2 → Type uW` with `AddCommGroup` and `Module ℂ` instances, every
   `τ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i)`, the
   hypothesis `∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (τ i)`,
   and every `ell : ∀ i, glInverseFunctionals ψ (m i) (τ i)`, there is
   `C : ℝ` such that for every `u : ℝ` with `C < u` the following holds.
7. For every section
   `f : TwoBlockJacquet.Sections F h (twoBlockOppositeTwistBlocks F m τ u)`,
   every carrier `V : Type uV` with `AddCommGroup` and `Module ℂ` instances,
   every `π : Representation ℂ (GeneralLinear (t + 1) F.Carrier) V`, the
   hypothesis `IsSmooth π`, every `ℓ : glFunctionals ψ t π`, every
   `Wtest : (coefficientModel π ℓ).toSubmodule`, every
   `Φ : SchwartzBruhat (Fin (t + 1) → F.Carrier)` and every `k : ℤ`, put

   ```text
   E     = TwoBlockUnfolding.integrand
             (fun i => twoBlockOppositeTwistFunctional F m ψ τ u i (ell i)) f Wtest.val Φ
   slice = RankinSelberg.determinantSlice T t k            : Set NQ
   Hslice = projection h F.Carrier ⁻¹' slice                : Set HQ
   A     = radicalAverage F h μR E                          : NQ → ℂ
   Aabs  = radicalAverage F h μR (fun z => (‖E z‖ : ℂ))     : NQ → ℂ
   ```

   The conclusion is the conjunction

   ```text
   Measurable E ∧ Measurable A ∧ Measurable Aabs ∧
   (∀ g : G, Integrable (fun x => E (fiberPoint h F.Carrier x g)) μR) ∧
   (∀ g : G, A (Quotient.mk _ g) =
     Wtest.val.val g * TwoBlockJacquet.jacquetFunction ψ (fun i => (ell i).val) μR f g *
       Φ (lastRow g)) ∧
   ∀ (νN : Measure NQ) (νH : Measure HQ),
     IsCompatible N μG μN νN → IsCompatible H μG μH νH →
     Integrable E (νH.restrict Hslice) ∧
     Integrable Aabs (νN.restrict slice) ∧
     Integrable A (νN.restrict slice) ∧
     (∫ q, A q ∂νN.restrict slice) = c.toReal • (∫ z, E z ∂νH.restrict Hslice)
   ```

The field universe `uF`, the test-representation carrier universe `uV` and
the block-carrier universe `uW` are independent.

## Meaning of the objects

- `twoBlockOppositeTwistBlocks F m τ u i` is `τ i` twisted by
  `|det|^(-u)` for `i = 0` and by `|det|^u` for `i = 1`, on the same carriers.
  `twoBlockOppositeTwistFunctional F m ψ τ u i (ell i)` is `ell i` with the
  same linear map, as an inverse-character functional of the twisted block
  (`twoBlockOppositeTwistFunctional_val`, proved by `rfl`). This is why the
  Jacquet function in the representative identity is written with
  `fun i => (ell i).val`.
- `TwoBlockJacquet.Sections F h σ` is the carrier of the actual lower
  normalized induction of `σ_0 ⊗ σ_1`, the sections of JPSS (4.6.1).
- `IsOfWhittakerType` is the published JPSS §2.1 notion: admissible, finitely
  generated, and a one-dimensional space of functionals for the given
  character. It does not require irreducibility. `IsSmooth π` says every
  vector is fixed by some open subgroup.
- `glFunctionals ψ t π` is the space of standard Whittaker functionals of `π`,
  and `coefficientModel π ℓ` is the image of `v ↦ (g ↦ ℓ(π(g)v))`. So
  `Wtest.val.val g = ℓ(π(g)v)` for some vector `v`.
- `E` is the published descended function on `HQ` with
  `E [g]_H = Wtest(g) · f[g; e, e] · Φ(lastRow g)` (`integrand_mk`), where
  `f[g; e, e]` contracts `f(g)` with the two functionals at the Levi identity.
- `fiberPoint h F.Carrier x g` is the coset `[u(x) g]_H`, with `u(x)` the upper
  radical element `(1 x; 0 1)`. By the published `integrand_fiberPoint`,
  `E (fiberPoint x g) = Wtest(g) · (raw Jacquet integrand at g, x) · Φ(lastRow g)`,
  and the raw integrand is `f[u(x) g; e, e] ψ(x_(m 0, 0))`.
- `radicalAverage F h μR F'` is the published descent to `NQ` of
  `g ↦ ∫ x, F' (fiberPoint x g) ∂μR`. Its `IsAddHaarMeasure` argument for `μR`
  is the published instance `rectangularMeasure_isAddHaar`. So `A` is the
  inner integral of (4) times `Φ(ηg) W(g)`, and `Aabs [g]` is the absolute
  fiber integral `∫ ‖E (fiberPoint x g)‖ dμR(x)`, as a complex number.
- `slice` is the published determinant slice
  `{N g : T.ord (det g) = k}`, which `mk_mem_determinantSlice_iff_normalizedAbs`
  identifies with the source condition `|det g| = q^(-k)`. It is the source's
  `N \ G^m` with `m = k`. `Hslice` is its inverse image under the published
  projection `HQ → NQ`, the source's `N_(t_1,t_2) \ G_r^m`.
- `IsCompatible H μG μH ν` is the published compatibility of a quotient
  measure: `ν ≠ 0`, `ν` regular, invariant under all right translations, and
  the Weil formula `∫ (orbital average of f) dν = ∫ f dμG`, with integrability
  of the orbital average, for compactly supported continuous `f : G → ℂ`.

## Reading of the conclusions

- `Measurable E`, `Measurable A` and `Measurable Aabs` are the measurability
  needed for the outer integrals. They are conclusions, not premises.
- The fiber clause says that the inner integral of (4) converges absolutely at
  every representative `g`, after multiplication by `Wtest(g) Φ(lastRow g)`.
- The representative clause identifies the radical average with
  `W(g) W'(g) Φ(ηg)`, the integrand of (4). It is the published
  `TwoBlockUnfolding.radicalAverage_integrand_mk` applied to the twisted
  functionals; the author checked this by compiling a proof outside this
  module. It is kept as a conclusion so that the Bochner identity below can be
  read as the source's identity between (4) and the first integral on page 412.
- For every compatible pair `νN`, `νH`, the last clause states absolute
  integrability of `E` on `Hslice`, absolute integrability on `slice` of the
  absolute fiber integral `Aabs` and of `A`, and the Bochner identity

  ```text
  ∫_(slice) A dνN = c.toReal • ∫_(Hslice) E dνH.
  ```

  Because integrability is asserted on both sides, this is not an equality of
  totalized Bochner integrals that could both be zero by convention. The
  integrability of `Aabs` is the source's "the integral in (4) is absolutely
  convergent".

## Quantifier order and the bound

The measure assertions about `c`, right invariance and existence of
compatible measures come first and do not depend on any representation. The
bound `C` is chosen after `τ` and `ell`. It may depend on `p`, `F`, `ψ`, `ν`,
`t`, `m`, `h`, `τ` and `ell`. It does not depend on `u`, the section `f`, the
test representation `π`, the functional `ℓ`, the coefficient `Wtest`, the row
function `Φ`, the slice index `k` or the quotient measures. The source's
`u ≫ 0` concerns the blocks only, and the published Jacquet convergence
statement has the same order. The conclusions are required for every real
`u > C` with the exact published twisted blocks and functionals.

The zero functional is allowed for each `ell i`. Then the contraction
`f[g; e, e]` vanishes, so `E`, `A` and `Aabs` are identically zero and every
conclusion holds trivially. Zero `ℓ`, zero `Wtest` and zero `Φ` behave the
same way. No premise excludes them.

## Normalization factor

The factor `c` is the `μR`-mass of the matrices with integral entries. Because
`μR` is the product of copies of the self-dual measure `ν.val`, `c` equals
`ν.val(O)` raised to the power `(m 0 + 1)(m 1 + 1)`. The self-dual measure
depends on `ψ`, so `c` is not `1` in general. Thus `c = 1` exactly when
`ν.val(O) = 1`; the published `rectangularMeasure_entries_one` proves the
"if" direction. The
statement keeps `c`, its bounds `0 < c < ⊤` and the supplied `μR` unchanged.
It neither rescales `μH` nor imposes a mass-one condition.

The direction of the factor is that of the published
`TwoBlockUnipotentQuotientIntegrationStatement`. In the coordinates
`(a, x) ↦ a · u(x)` from `H × R` to `N`, the integral points have mass `c`
under `μH ⊗ μR`, since both block groups give their integral points mass one.
They have mass one under `μN`. The source writes its unfolding "formally"
with unnamed measures, and its identity has no explicit constant. The factor
`c` is the result of the project's fixed normalizations.

## Scope compared with the source

**Test representation.** In JPSS, `π` is a representation of Whittaker type
(§2.1, p.385, and §3.1, p.404, as cited in the published Markdown of
`WhittakerRowSliceCompactSupportStatement`) and `W` lies in its Whittaker space `W(π; ψ)`. Here
`π` is every smooth representation on a carrier in an independent universe,
`ℓ` is every standard Whittaker functional of `π`, including zero, and
`Wtest` is every element of the actual coefficient image. A representation of
Whittaker type is admissible, hence smooth, so the source's test
representations are included. This all-smooth-test scope is a derived
strengthening made inside the project, not a statement of the source. It
matches the published `WhittakerRowSliceCompactSupportStatement`, which
states fixed-slice compact support for actual coefficient images of all
smooth representations. The coefficient images are actual: an arbitrary
`ψ`-equivariant function need not be smooth, and the analytic argument
below needs smoothness.

**Blocks.** The blocks `τ i` are any representations of full standard
Whittaker type, reducible ones included. The source's sections take values in
`W(τ_1; ψ̄) ⊗ W(τ_2; ψ̄)` and evaluate at `(e, e)`. Here the block carriers are
abstract and the evaluation is replaced by arbitrary inverse-character
functionals `ell i`, as in the published integrand and Jacquet convergence
modules.

**No added premises.** The proposition adds no irreducibility, no
compactness of the support of `f`, no pointwise convergence, no
integrability, no other Haar normalization, no chosen quotient representative
and no factor identity. It quantifies every integer slice and every real
parameter above the bound.

## Provenance of the analytic content

The source's one-sentence justification uses three ingredients. The first
two are stated in the Library; the third is the extra step this statement
makes explicit. This is a route for a later proof; this module does not claim
that the existing data identities or the compact-support statement alone
prove the proposition.

1. **Fixed-slice compact support.** The published statement
   `WhittakerRowSliceCompactSupportStatement` asserts that, for every smooth
   `π`, standard functional, actual coefficient `W`, Schwartz–Bruhat `Φ` and
   `k`, the function `N g ↦ ‖W(g)‖ ‖Φ(lastRow g)‖` restricted to the slice has
   compact support in `NQ`. This is the source's "compactly supported modulo
   `N_r`". Its proof is the separate task `8459a926`.
2. **Ordinary convergence for large `u`.** The published theorem
   `Langlands.RankinSelberg.twoBlockJacquetConvergence` proves
   `TwoBlockJacquetConvergenceStatement`: for nonzero `ell` there is `C` such
   that for `u > C` the raw Jacquet integrand of every section is
   `μR`-integrable at every `g`. With `integrand_fiberPoint` this gives the
   fiber clause; for zero `ell` it is trivial. This is pointwise convergence
   of the inner integral only.
3. **Local constancy and local boundedness.** Pointwise finiteness of `Aabs`
   and compact support of `‖W‖ ‖Φ ∘ lastRow‖` do not by themselves make `Aabs`
   integrable on the slice: one also needs `Aabs` bounded on that compact set.
   The intended argument is smoothness. `Wtest` is right invariant under an
   open subgroup because `π` is smooth. The section `f` lies in the published
   `Induction.SmoothFunctions`, so `g ↦ f(g)` is right invariant under an open
   subgroup; equivalently, by the published `TwoBlockJacquet.integrand_inducedRep`,
   the raw Jacquet integrand at `g k` equals that at `g` for `k` in it. The
   function `Φ ∘ lastRow` is right invariant under an open subgroup as well:
   if `Φ` is supported in `ϖ^(-b) O^(t+1)` and constant on cosets of
   `ϖ^a O^(t+1)`, it is invariant under `k ∈ GL_(t+1)(O)` with
   `k - 1 ∈ ϖ^(a+b) M_(t+1)(O)`, because such `k` preserve the norm of row
   vectors. Hence the function on `G` defining `E` is right invariant under
   an open subgroup `K`, and `E` is locally constant, hence measurable. By
   the published `radicalAverage_rightTranslate`, `A` and `Aabs` are also
   right `K`-invariant on `NQ`, hence locally constant and measurable. By
   `integrand_fiberPoint`, `‖A [g]‖ ≤ Aabs [g] = ‖Wtest(g)‖ ‖Φ(lastRow g)‖`
   times the finite absolute Jacquet integral at `g`, so both vanish outside
   the support of `‖Wtest‖ ‖Φ ∘ lastRow‖`, which is compact on the slice by
   step 1. A locally constant finite function is bounded on a compact set,
   and the slice is clopen (`isClopen_determinantSlice`). So `A` and `Aabs`
   restricted to the slice are continuous with compact support, and they are
   integrable for the regular measure `νN`, which is finite on compact sets.
4. **Tower.** The published `TwoBlockUnipotentQuotientIntegrationStatement`,
   whose proof is task `216195e1`, supplies a kernel `κ` from `NQ` to `HQ`
   with `κ [g]_N` the image of `μR` under `x ↦ fiberPoint x g`. It gives the
   criterion that a measurable `E` is integrable on `Hslice` if almost every
   fiber is integrable and `q ↦ ∫ ‖E‖ dκ(q)` is integrable on `slice`; this
   function is the real part of `Aabs`. For such `E` it gives the Bochner
   identity with factor `c.toReal`.

## What is not asserted

- No proof of the proposition, and no claim that compact support, the
  Jacquet convergence theorem or the published total-integral identities
  prove it without the local boundedness argument and the tower.
- No integrability over all of `NQ` or `HQ`, no summation over `k` and no
  Laurent series. Only fixed determinant slices are treated.
- Nothing about display (6), formula (7), partial Fourier or Mellin
  identities, functional equations, or gamma and L-factor identities.
- No continuity statement beyond the stated measurability, and no uniformity
  of the support in `Wtest`, `Φ` or `k`.

The module imports the published `TwoBlockUnfoldingIntegrandData`,
`TwoBlockUnipotentQuotientIntegrationStatement`,
`TwoBlockJacquetConvergenceStatement` and
`WhittakerRowSliceCompactSupportStatement` unchanged and changes no existing
Library pair.
