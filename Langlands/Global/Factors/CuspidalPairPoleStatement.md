# Poles and vertical-strip bounds of completed cuspidal pair L-functions

Author: Worker 3657. Statement contribution to task
`34b81620-20d7-4059-9b08-6bedd1c1c029`, revision 1.

**Scope.** This module states one proposition, uses eight auxiliary
declarations (one structure and seven definitions), and proves nothing:

- `Langlands.Global.CuspidalPairPoles.IsPositiveArchimedeanScalar`;
- `Langlands.Global.CuspidalPairPoles.IsTrivialOnSplitCentre`;
- `Langlands.Global.CuspidalPairPoles.FinitePairLChoice`, with
  `FinitePairLChoice.ofFactorChoice`, `FinitePairLChoice.finiteL` and
  `FinitePairLChoice.IsCompletedLFunction`;
- `Langlands.Global.CuspidalPairPoles.HasSimplePoleProfile`;
- `Langlands.Global.CuspidalPairPoles.IsBoundedInVerticalStrips`;
- `Langlands.Global.CuspidalPairPoleStatement`.

The module is `Langlands.Global.Factors.CuspidalPairPoleStatement`. The
proposition is the part of Getz–Hahn (2024), Theorem 11.7.1, that the published
`CuspidalPairGlobalFunctionalEquationStatement` leaves out: the completed
Rankin–Selberg L-function `Λ(s, π × π')` of two cuspidal representations trivial
on `A_GL` is holomorphic except for at most simple poles at `s = 0, 1`. It has
poles there exactly when the ranks agree and `π ≅ π'^∨`, and it is bounded in
vertical strips. The established form followed is Cogdell (2004), Theorem 4.1
(item 2) and Theorem 4.2.

The finite-place vocabulary (`residueCardinality`,
`HasIrreducibleAdmissibleComponents`, `localClass`, `FinitePairFactorChoice`) is
that of the published `CuspidalPairFactorData`. The archimedean factors are
those of the published functional-equation statement. Nothing from those modules
is rebuilt.

**Why it is here.** `CuspidalPairFunctionalEquationStatement.md` §6 says that
poles and boundedness in vertical strips are not stated there and "belong to
other tasks". The program ledger `notes/automorphic/global-program-coverage.md`
(section "13 November 2026 carry-over") lists this pole part of GH Thm 11.7.1
as an L4 target of this program with no public statement. It is the input for
the pole-order formula of GH Lemma 11.8.1 and for strong multiplicity one
(GH Thm 11.7.2, which GH p.309 calls a consequence of Thms 11.5.2 and
11.7.1).

**Proof target.** A later proof task should prove the Library statement
`Langlands.Global.CuspidalPairPoleStatement`. Its universe parameters are `u`
(the number field) and `uQ` (the factor universe of the spectral presentations).

## 1. Sources

"p." is the printed page and "PDF" the one-based page of the registered file.

| Source ID | Short name | Locators used |
|---|---|---|
| `getz-hahn-2024-automorphic-representations` | GH | (2.20) and the examples after it, p.68 (PDF 85); (11.23)–(11.24) p.308 (PDF 319); norm shift and Thm 11.7.1, p.309 (PDF 320); Lemma 11.8.1, p.312 (PDF 323) |
| `cogdell-2004-analytic-theory-gln` | Cog04 | definition of the local L-factor and its independence of `ψ`, Thm 3.1 p.213 (PDF 216); global setup p.218 (PDF 221); Thm 4.1 p.219 (PDF 222); vertical strips pp.220–221 (PDF 223–224); Thm 4.2 p.222 (PDF 225) |

**What the sources state.** GH Thm 11.7.1 (p.309): "Assume that `π` (resp.
`π'`) is trivial on `A_GLn` (resp. `A_GLm`). The Rankin–Selberg L-function
admits a meromorphic continuation to the plane, holomorphic except for possible
simple poles at `s = 0, 1`. It is bounded in vertical strips. There are poles at
`s = 0, 1` if and only if `m = n` and `π ≅ π'^∨`. One has a functional equation
(11.25)." GH cites Cog07, Theorems 4.1 and 4.2, for it. Here `π`, `π'` are
cuspidal automorphic representations of `GL_n(𝔸_F)`, `GL_m(𝔸_F)`, and the
L-function is the product over all places, archimedean ones included, of
(11.23) (p.308).

Cog04 states the same results for unitary cuspidal `π`, `π'` (p.218), again for
the product over all places:

- Thm 4.1 (p.219), item 2: "the extended function is bounded in vertical strips
  (away from its poles)";
- Thm 4.2 (p.222): if `m < n`, `L(s, π × π')` is entire; if `m = n`, it has at
  most simple poles, and they occur if and only if `π ≅ π̃' ⊗ |det|^(iσ)` with
  `σ` real, and are then at `s = -iσ` and `s = 1 - iσ`.

Cog04 pp.220–221 obtains the bound in vertical strips from the global integrals
for `m = n - 1` and `m = n`. For the other ranks it refers to Gelbart and
Shahidi's theorem on L-functions from Eisenstein series (its reference [12]).

**`A_GL`.** GH (2.20) (p.68) defines `A_G` for a number field as the neutral
component of the real points of the greatest `ℚ`-split torus in `Res_(F/ℚ) Z_G`.
For `G_m` it is the image of the diagonal embedding `ℝ_(>0) → F_∞^×`, regarded in
`𝔸_F^×`; and `A_(GL_n) = {a I_n : a ∈ A_(G_m)}`.

## 2. Declarations

Namespace `Langlands.Global.CuspidalPairPoles`. Except in
`IsPositiveArchimedeanScalar`, the field `F` is a number field with
`[CompactSpace (AdeleQuotient F)]`, the instance needed by
`CuspidalOperatorRealization`.

### `IsPositiveArchimedeanScalar a`

For an idele `a : IdeleGroup (𝓞 F) F` (Mathlib's `𝔸_F^×`, whose underlying adele
is a pair of an infinite and a finite adele):

1. the finite component of `a` is `1`;
2. for some real `t > 0`, at every infinite place `v` the `v`-component `a_v` of
   `a` satisfies `extensionEmbedding v a_v = t`.

`InfinitePlace.Completion.extensionEmbedding v : F_v →+* ℂ` is Mathlib's
injective embedding of the completion. The real number `t` is fixed by complex
conjugation, so clause 2 says that `a_v` is the real number `t` in `F_v`
whichever embedding is used. So the predicate describes exactly the image of
`ℝ_(>0)` in `𝔸_F^×` of GH (2.20), that is, `A_(G_m)`.

### `IsTrivialOnSplitCentre T`

For a cuspidal realization `T` of `GL_(r+1)`: for every `a` with
`IsPositiveArchimedeanScalar a`, every vector `f` of `T` and every
`x ∈ GL_(r+1)(𝔸_F)`, the function of `f` takes the same value at
`AdelicGL.scalar F (r + 1) a * x` and at `x`. `AdelicGL.scalar` sends an idele
to the scalar matrix. This says that `T` is trivial on
`A_(GL_(r+1)) = {a I : a ∈ A_(G_m)}`, the hypothesis of GH Thm 11.7.1. The
scalar matrices are central, so left and right translation agree here.

### `FinitePairLChoice P P' h h'`

A choice, at every finite place `v`, of:

- a nontrivial additive character `additive v` of `F_v`;
- a self-dual measure `measure v` for it (`measure_spec`);
- a polynomial `lPolynomial v` with `IsAutomorphicPairLPolynomial` for the
  canonical p-adic classes `localClass P h v` and `localClass P' h' v`
  (`lPolynomial_spec`). This is the JPSS pair L-polynomial of the local
  components, as in `FinitePairFactorChoice`.

These are the L-polynomial fields of `FinitePairFactorChoice` without the
global character `ψ`, the dual pair and the ε-factors, which the pole statement
does not use. The local characters are arbitrary. This loses nothing: the JPSS
L-factor does not depend on the additive character (Cog04 p.213). For fixed
data the polynomial is unique (`IsLanglandsPairLPolynomial.unique`).

`FinitePairLChoice.ofFactorChoice c` forgets a `FinitePairFactorChoice ψ P P' Pd Pd'
h h' hd hd'` to its L-polynomial data. So a consumer that holds the data of the
functional equation can apply this statement to the same finite factors.

### `c.finiteL v s`

`((c.lPolynomial v).eval (q_v^(-s)))⁻¹`, that is,
`L(s, Π_v × Π'_v) = 1 / P_v(q_v^(-s))`. Here `q_v = residueCardinality v` and
`q_v^(-s)` is `RankinSelberg.spectralPoint q_v s`. It is the same expression as
`FinitePairFactorChoice.finiteL`.

### `c.IsCompletedLFunction Linf Λ`

For some real `σ` and every `s` with `σ < Re s`: the sum
`∑_v ‖c.finiteL v s - 1‖` over the finite places converges, and the Euler
product `∏_v c.finiteL v s` has a value `p` (`HasProd`) with `Λ s = Linf s * p`.
This is the completed L-function of GH (11.23) with archimedean part `Linf`.
The convergence clause has the form of `CompletedEquationHolds` in
`CuspidalPairFactorData`.

### `HasSimplePoleProfile Λ cond`

1. `Λ` is complex-differentiable on `ℂ \ {0, 1}`;
2. at `s = 0` and at `s = 1`, `Λ` is meromorphic,
   `-1 ≤ meromorphicOrderAt Λ s`, and `meromorphicOrderAt Λ s < 0` holds
   exactly when `cond` holds.

Mathlib's order convention: zeros have positive order, poles negative order, and
`⊤` is the order of a function vanishing identically near the point. So clause 2
says that the only possible poles are simple ones at `0` and `1`, present
exactly under `cond`. The values `Λ 0` and `Λ 1` are not constrained, and
`meromorphicOrderAt` ignores them.

### `IsBoundedInVerticalStrips Λ`

For all real `a`, `b` and every `ε > 0` there is `C` such that `‖Λ s‖ ≤ C`
whenever `a ≤ Re s ≤ b`, `ε ≤ ‖s‖` and `ε ≤ ‖s - 1‖`. This is Cog04's "bounded
in vertical strips (away from its poles)" with the two possible poles. When
there is no pole at `0` or `1`, the excluded disc there is compact and `Λ`
extends holomorphically across it. So the predicate loses nothing in that case
either.

### `CuspidalPairPoleStatement`

The hypotheses are:

- a number field `F`, ranks `r`, `t`;
- actual cuspidal realizations `T` of `GL_(r+1)` and `T'` of `GL_(t+1)`, both
  with `IsTrivialOnSplitCentre`;
- spectral presentations `P`, `P'` of them, with irreducible admissible finite
  local components (`h`, `h'`).

The conclusion has two conjuncts.

1. **Existence of the data.** `FinitePairLChoice P P' h h'` is nonempty, and at
   every real (complex) place both realizations have a real (complex)
   standard-module parameter.
2. **The analytic properties.** For every choice `c`, all parameter families
   `dR`, `dR'` at the real places and `dC`, `dC'` at the complex places of `T`
   and `T'`, put

   `L∞(s) = ∏_(v real) (realPairLFactor (dR v) (dR' v)).denominator(s)⁻¹ ·
   ∏_(v complex) (complexPairLFactor (dC v) (dC' v)).denominator(s)⁻¹`.

   Then some `Λ : ℂ → ℂ` satisfies `c.IsCompletedLFunction L∞ Λ`,
   `HasSimplePoleProfile Λ cond` and `IsBoundedInVerticalStrips Λ`. The pole
   condition `cond` is `∃ hrt : r = t, IsContragredientOf (hrt ▸ T.realization)
   T'.realization`: the ranks agree and, after transport along `r = t`, `T`
   realizes the contragredient of `T'`. This is GH's `m = n` and `π ≅ π'^∨`.

`L∞` is exactly the archimedean factor of the published
`CuspidalPairGlobalFunctionalEquationStatement` (its Markdown §3 explains the
parameters, the Tate factors and the convention `0⁻¹ = 0` at archimedean poles).
The Euler-product identity is only required on a right half-plane, where
`σ` may be chosen to the right of the archimedean poles.

**Uniqueness of `Λ`.** Two functions with `IsCompletedLFunction` agree on a
right half-plane. Both are holomorphic on the connected open set
`ℂ \ {0, 1}`, so they agree there by the identity theorem. So the statement is
about the completed L-function itself; only the values at `0` and `1` are
free.

## 3. Hypotheses and their match with the source

- **Cuspidal realizations.** `CuspidalOperatorRealization F r` is an actual
  irreducible cuspidal subspace of automorphic forms on `GL_(r+1)`, and `r + 1`,
  `t + 1` are GH's `n`, `m`.
- **Trivial on `A_GL`.** This is GH's hypothesis, stated through
  `IsTrivialOnSplitCentre`. It cannot be dropped. GH p.309 records the norm shift
  `L(s, π|det|^(s₁) × π'|det|^(s₂)) = L(s + s₁ + s₂, π × π')`, which moves the
  poles to `-s₁ - s₂` and `1 - s₁ - s₂`. For example, with `F = ℚ`, `π = 1` and
  `π' = |·|^(-1)` on `GL_1`, the completed L-function is `Λ_ℚ(s - 1)`, which has
  poles at `s = 1, 2`, and `π' ≇ π^∨`.
- **Relation to Cog04's unitarity.** Cog04 assumes unitary cuspidal
  representations. Triviality on `A_GL` implies it: the central character is then
  trivial on `ℝ_(>0)`, hence a character of the compact group
  `F^× \ 𝔸_F^× / ℝ_(>0)`, hence unitary; and a cuspidal realization with a
  unitary central character is unitarizable (in the Library,
  `CuspidalOperatorRealization.isUnitarizable_of_hasUnitaryCentralCharacter`,
  module `Langlands.Automorphic.CuspidalUnitaryForm`). Conversely, for unitary `π'` the
  representations `π̃' ⊗ |det|^(iσ)` of Cog04 Thm 4.2 with `σ ≠ 0` are not
  trivial on `A_GL`, since `|det(a I_n)|^(iσ) = t^(i σ n [F:ℚ])` for
  `a ∈ A_(G_m)` with real component `t`. So under GH's hypothesis Cog04's
  condition reduces to `σ = 0`, and Cog04's poles to `s = 0, 1`.
- **Direction of the contragredient.** GH writes `π ≅ π'^∨`.
  `IsContragredientOf T S` says that `T` realizes the contragredient of `S`, so
  the condition is `IsContragredientOf T T'`, with `T` cast to rank `t + 1`.
- **Presentations.** The finite factors are read from the spectral presentations,
  as in the published functional-equation statement. The hypothesis
  `HasIrreducibleAdmissibleComponents` is the same one used there.

## 4. Normalizations

- **Finite factors.** JPSS pair L-polynomials of the canonical p-adic classes,
  with `q_v^(-s)`, as in `CuspidalPairFactorData.md` §4. GH (11.23) and Cog04
  p.218 use these local factors.
- **Archimedean factors.** As in `CuspidalPairFunctionalEquationStatement.md` §3:
  Tate's factors of the block decomposition of the standard-module parameters,
  which Cog04 §3.2 and Jacquet (2009) identify with the archimedean
  Rankin–Selberg factors.
- **Region of convergence.** Only some right half-plane is asserted. The sharp
  region `Re s > 1` (GH p.309) is not stated.

## 5. Content beyond the source, and provenance

- **Existence conjunct.** As in the functional-equation statement, the first
  conjunct asserts that the data exist, so that the second is not vacuous, in
  the form `CuspidalPairFactorData.md` §8 describes. The finite data exist by the
  local theory: nontrivial characters and self-dual measures exist, and the
  JPSS L-factor exists (Cog04 Thm 3.1, p.213). The archimedean parameters exist
  because local components of cuspidal representations are generic
  (`CuspidalPairFunctionalEquationStatement.md` §3).
- **Universal over choices.** GH speaks of "the" L-function. By the uniqueness of
  the local L-factors and of `Λ` (§2), quantifying over every choice adds no
  mathematical content.
- **Bounded away from the poles.** GH says "bounded in vertical strips"; Cog04
  adds "away from its poles". The latter is stated, and it is the only meaningful
  form when there are poles.
- **Hecke twists.** Twists `T ⊗ (χ ∘ det)` by finite-order Hecke characters
  (the Library's `CuspidalOperatorRealization.determinantTwist`) remain trivial
  on `A_GL`, because a finite-order character is trivial on the connected group
  `ℝ_(>0)`. So the statement applies to them once their realizations and
  presentations are supplied. It does not state the general norm-shift
  reduction.
- **Not included.** The functional equation (published separately), zeros, the
  partial L-function on `Re s = 1` (`CuspidalPairBoundaryNonvanishingStatement`),
  isobaric pairs, and Lemma 11.8.1 are not stated here.

## 6. Proof routes (for the proof task)

Cog04 §4 (pp.219–222) proves the theorem through global Rankin–Selberg
integrals. As recalled on p.221 from Cog04 §2, for `m < n` the global
integrals `I(s; φ, φ')` are entire, and for `m = n` the integrals
`I(s; φ, φ', Φ)`, formed with an Eisenstein series built from a Schwartz
function `Φ`, have at most simple poles, at the points of Thm 4.2. The
integrals are products of local ratios at the places of `S` with `L(s, π × π')`,
and the local ratios can be chosen nonzero at any given point. So the poles of
`L` are exactly those of the family of integrals (pp.221–222). The
bound in vertical strips comes from the absolute convergence of the integrals
for `m = n - 1, n` (pp.220–221), and in general from Gelbart–Shahidi. This needs:

- the global Rankin–Selberg integrals and their unfolding (Cog04 §2);
- the Eisenstein series of `GL_n` with Schwartz data and its poles;
- the local theory at all places, including the archimedean theory of Jacquet
  (2009);
- the Whittaker expansion of cusp forms, published in the Library as the
  unproved `Langlands.Global.WhittakerExpansionStatement`.

None of these is proved in the Library. The proof task may choose another
established route, and it must record the route it uses.
