# Matrix functional equation on a Whittaker model ⇒ rank-one JPSS gamma factor

Authors: Worker 901 (Lean statement and Markdown) and Worker 704 (independent
source audit of JPS 1979 and audit of this Markdown against the Lean and the
source).

This module defines one proposition,
`Langlands.RankinSelberg.RankOneMatrixFunctionalEquationComparisonStatement.{uF,uV}`.
It is a statement target, not a proof; compiling it only checks that the
proposition is well typed. It is a conditional form of JPS 1979, Section 4.4
and Theorem (4.5), for the trivial character of `GL_1` and every rank,
including rank one. A normalized Godement–Jacquet matrix functional equation
on the coefficient model of one nonzero Whittaker functional is the premise.
The conclusion is the full published JPSS gamma-factor relation of the
original representation against the trivial rank-one test. The premise is
not claimed to hold for any representation, and the statement is not an
unconditional analytic theorem.

## Quantifiers and installed structures

The proposition quantifies, in this order, over:

1. every prime `p` with `[Fact p.Prime]` and every `F : PadicField.{uF} p`.
   The statement then installs by `letI`/`haveI` the canonical topology,
   valuative relation and nonarchimedean local-field structure of
   `F.Carrier` from `F.canonicalTopologicalData`, the Borel measurable space
   `borel F.Carrier` with `BorelSpace`, `T2Space` (the published field
   `F.canonicalTopologicalData.fieldT2`) and `TotallyDisconnectedSpace`
   (derived inline from `ValuativeRel.nonarchimedeanRing`). The last two are
   needed only because `HarmonicAnalysis.IsSelfDual` requires them. The
   telescope is the one of the published
   `GodementJacquet.TwoBlockMatrixFunctionalEquationInductionStatement`. All
   installed classes are either the canonical data used inside the `Padic`
   wrappers of the premise and the conclusion, or propositions, so no choice
   of instance changes the meaning;
2. every `ψ : HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier`. The
   structure bundles continuity, unitarity and the field `nontrivial`, so
   `ψ` is nontrivial without a separate hypothesis;
3. every `ν : HarmonicAnalysis.AdditiveHaarMeasure F.Carrier` with the
   premise `HarmonicAnalysis.IsSelfDual ψ ν`. This same `ν` is passed both
   to the matrix premise and to the gamma conclusion; no other additive
   measure occurs;
4. every `n : ℕ`, including `n = 0`, so the representation has rank
   `n + 1 ≥ 1`;
5. every carrier `V : Type uV` with explicit instances `AddCommGroup V` and
   `Module ℂ V`, and every actual
   `σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V`
   with the premise `Whittaker.IsOfWhittakerType n (standardCharacter ψ n) σ`.
   The universes `uF` and `uV` are independent;
6. every `ℓ : Whittaker.glFunctionals ψ n σ` with `ℓ.val ≠ 0`;
7. every `P PDual : Polynomial ℂ`, `c : ℂˣ` and `a : ℤ`, with the premise

   ```text
   GodementJacquet.Padic.NormalizedMatrixFunctionalEquationData F ψ ν
     (V := (glCoefficientModel ψ n σ ℓ).toSubmodule)
     (glModelRepresentation ψ n σ ℓ) P PDual c a.
   ```

The conclusion is exactly

```text
IsPadicSymmetricGammaFactor F ψ ν σ
  (rankOneCharacter (1 : F.Carrierˣ →* ℂˣ))
  (rationalGammaExpression (LocalFactor.residueReflection F) c a P PDual).
```

The contract writes `psi`, `nu`, `sigma`, `ell`; the Lean binders are `ψ`,
`ν`, `σ`, `ℓ`.

## The representation premise

`IsOfWhittakerType n (standardCharacter ψ n) σ` (from
`RankinSelberg.AnalyticStatement`) is the conjunction of `IsAdmissible σ`
(which includes smoothness), finite generation of `σ.asModule` over the
group algebra `MonoidAlgebra ℂ (GL(n+1))`, and a linear equivalence between
the whole space of standard Whittaker functionals and `ℂ`. Irreducibility,
a model equivalence, induced type, finite length, a central character,
matrix analytic existence and any gamma-factor certificate are not assumed.
Reducible `σ` of full Whittaker type are included.

## The matrix premise, unfolded

`glCoefficientModel ψ n σ ℓ` is the published coefficient image of `ℓ`: the
space of functions `g ↦ ℓ(σ(g) v)` on `GL(n+1)`, `v ∈ V`. Its elements are
`ψ`-Whittaker functions. `glModelRepresentation ψ n σ ℓ` is right translation
on this space. The premise is about this representation, not about `σ` on
the original carrier `V` and not about any other representation.

`Padic.NormalizedMatrixFunctionalEquationData F ψ ν ρ P PDual c a`, from
`GodementJacquet.AnalyticData`, uses the canonical residue cardinality `q`,
the normalized absolute value, the Borel structure on `GL(n+1)` and the
shared Haar measure `generalLinearHaar F.Carrier n`. For `ρ` the model
representation it is the conjunction of:

- `MatrixAnalyticAssertions ρ P`: one real bound beyond which
  `Z(Φ, s + n/2, f) = ∫ Φ(g) f(g) |det g|^(s + n/2) dg` converges absolutely
  for every Schwartz–Bruhat function `Φ` on all `(n+1) × (n+1)` matrices
  and every actual bi-smooth matrix coefficient `f` of `ρ`; for every
  `(Φ, f)` a rational function `R` with `HasShiftedRationalValue`, i.e.
  actual agreement with `R(q^(-s))` on a right half-plane; and
  `IsNormalizedGenerator` for `P`: `P(0) = 1` and the Laurent span of all
  these continuations is generated by `P⁻¹`;
- `IotaMatrixAnalyticAssertions ρ PDual`: the same three conditions for the
  functions `coefficientIota f : g ↦ f(ᵗg⁻¹)`, with `f` running over the
  same coefficients, and generator `PDual`;
- for every `Φ` a Schwartz–Bruhat `ΦHat`, chosen before any coefficient, with
  `MatrixFourierPair ψ ν Φ ΦHat`: for every matrix `x`, the function
  `y ↦ Φ(y) ψ(Tr(y ᵗx))` is integrable for the product measure
  `rectangularMeasure ν (n+1) (n+1)` and `ΦHat(x)` is its integral. Then for
  every coefficient `f` and all `R`, `RDual` with `HasShiftedRationalValue`
  for `(Φ, f)` and for `(ΦHat, coefficientIota f)`,
  `NormalizedFunctionalEquation q P PDual 1 c 0 a R RDual` holds: for every
  `s` with `R.denom(q^(-s)) ≠ 0` and `RDual.denom(q^(-(1-s))) ≠ 0`,

  ```text
  PDual(q^(-(1-s))) · RDual(q^(-(1-s))) = c · (q^(-s))^a · P(q^(-s)) · R(q^(-s)).
  ```

So the original shift is `s + n/2`, the transformed integral is evaluated at
`1 - s + n/2`, and the pairing is the plus transpose pairing. `P`, `PDual`,
`c`, `a` are fixed before every test and coefficient.

## The conclusion, unfolded

**The gamma expression.** `rationalGammaExpression δ c a P PDual` (from
`RankinSelberg.PairFactors`) is the rational function
`c X^a · P(X) / PDual(δ / X)`. Here `δ = LocalFactor.residueReflection F`,
which coerces to `q⁻¹` (`coe_residueReflection`). At `X = q^(-s)` one has
`δ / X = q^(-(1-s))`, so the expression is
`c q^(-a s) P(q^(-s)) / PDual(q^(-(1-s)))`. This is the matrix gamma factor
`ε(s) L(1-s, dual)/L(s)` with `L(s) = 1/P(q^(-s))`, dual factor
`1/PDual(q^(-s))` and `ε(s) = c q^(-a s)` that the premise provides. It is
a reduced element of `RatFunc ℂ`; its denominator may be smaller than
`PDual(δ / X)` after cancellation.

**The symmetric wrapper.** `IsPadicSymmetricGammaFactor F ψ ν π τ G` (from
`RankinSelberg.PadicPairFactors`) for `π` of rank `r + 1` and `τ` of rank
`m + 1` is `IsPadicPairGammaFactor F ψ ν π τ G` when `m ≤ r` and the swapped
pair otherwise. Here `π = σ` (`r = n`) and `τ = rankOneCharacter 1`, the
trivial one-dimensional representation `1 ∘ det` of `GL_1` on `ℂ` (`m = 0`).
Since `0 ≤ n`, the conclusion is the pair relation for `(σ, rankOneCharacter 1)`.
`IsPadicPairGammaFactor` installs the Borel structures on `GL(0+1)`,
`upperUnipotent (0+1)` and `LeftUnipotentQuotient 0` and is
`IsPairGammaFactor q ψ abv ν σ (rankOneCharacter 1) G` with the canonical
`q` and normalized `abv`, and with the same `ν`.

**Positive rank `n > 0`.** `IsPairGammaFactor` is then
`IsUnequalRankGammaFactor (0 < n)`, the conjunction of:

- existence of the right-invariance instance for `unipotentHaar F 0` and of
  a measure on `LeftUnipotentQuotient 0` compatible with
  `generalLinearHaar F 0`;
- existence of a nonzero `ℓ₁ : glFunctionals ψ n σ`;
- existence of a nonzero `ℓ' : glInverseFunctionals ψ 0 (rankOneCharacter 1)`;
- for every such instance, every compatible quotient measure `μ`, every
  nonzero `ℓ₁` and every nonzero `ℓ'` (not only the supplied `ℓ`),
  `UnequalRankGammaEquation`: there is `ζ : ℂˣ` with
  `HasModelMinusOneScalar (rankOneCharacter 1) ℓ' ζ`, and for **every** pair
  `j, k` with `n = 0 + (j + k + 1)`:
  - some block-`j` integral of model vectors has a nonzero rational
    continuation, and
  - for every model vector `f` of `ℓ₁` and `f'` of `ℓ'` there are rational
    functions `R`, `Rdual` such that `R` continues the block-`j` integral
    `Ψ(s; f, f'; j) = ∫_{N₁\GL₁} ∫_{F^(j×1)} f(m(g, x)) f'(g) |det g|^(s - n/2) dx dμ`,
    with `m(g, x)` the block matrix `[g, 0, 0; x, I_j, 0; 0, 0, I_(k+1)]` and
    `dx = rectangularMeasure ν j 1`; `Rdual` continues the transformed
    block-`k` integral `dualUnequalRankModelIntegralAt`, which is the same
    integral with block `k`, `ψ⁻¹ = ψ.scale (-1)`, `rectangularMeasure ν k 1`,
    the second function `g ↦ f'(J_1 ᵗg⁻¹) = f'(g⁻¹)`, and the first
    function the right translate by the actual
    `blockWeylAt 0 n = diag(1, J_n)` of the first dual function
    `g ↦ f(J_(n+1) ᵗg⁻¹)` (`firstDualFunction`, a `ψ⁻¹`-Whittaker function).
    Here `J_m = GeneralLinear.weylLong m` is the *unsigned* permutation
    matrix with ones on the anti-diagonal; and `GammaFunctionalEquation q ζ n G R Rdual`
    holds: `Rdual(q^(-(1-s))) = ζ^n G(q^(-s)) R(q^(-s))` at every `s` where
    `R.denom(q^(-s))`, `Rdual.denom(q^(-(1-s)))` and the reduced
    `G.denom(q^(-s))` are nonzero.

For the trivial character, the model of `ℓ'` consists of constants and the
minus-one scalar is `1`.

**Rank one `n = 0`.** `IsPairGammaFactor` is then the equal-rank relation
`IsEqualRankGammaFactor (n := 0)` for `σ` and `rankOneCharacter 1`: the same
three existence clauses, and for every compatible `μ` and all nonzero
`ℓ₁`, `ℓ'` the `EqualRankGammaEquation`. It asks for a nonzero continuation
of some equal-rank integral, and for every `f`, `f'` and every
Schwartz–Bruhat `Φ` on `F¹` a row Fourier transform `Φhat`
(`IsRowFourierPair ψ ν Φ Φhat`, plus sign, same `ν`) and continuations `R`,
`Rdual` of
`∫_{N₁\GL₁} f(g) f'(g) Φ(lastRow g) |det g|^s dμ` and of the corresponding
integral of the two transformed functions with `ψ⁻¹` and `Φhat`, with
`GammaFunctionalEquation q ζ 0 G R Rdual` on the same reduced domain. This is
the `GL_1 × GL_1` Tate-type equation with the full Schwartz Fourier test.

The conclusion is not restricted to `ℓ`, to a chosen measure, to one block,
or to points where the uncancelled `P` and `PDual` are nonzero.

## Original source and exact correspondence

H. Jacquet, I. I. Piatetski-Shapiro and J. Shalika, *Automorphic forms on
GL(3) I*, Ann. of Math. 109 (1979), 169–212, registered as `jps-1979-gl3-i`,
file
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Automorphic Forms on GL(3) I--1979.pdf`,
SHA256 `6446822f267f9f95156ce7a193409209e56ce7858ed6d3d350480e73f35b1aa5`.
The one-based PDF page is the printed page minus 167. The source's `r` is
the rank `n + 1` here.

- Printed 174 (PDF 7), (0.4.2): the source's Weyl representatives are
  *signed*. With one-based indices, `w` has entries `w_(i, r+1-i) = (-1)^(i-1)`
  and zeros elsewhere; `w'` has `(1,1)` entry `(-1)^r` and, in rows and
  columns `2, ..., r`, anti-diagonal entries `(-1)^(r-2), ..., -1, 1` from
  top to bottom. For `r = 3`, `w' = [[-1,0,0],[0,0,-1],[0,1,0]]`, whereas
  `blockWeylAt 0 2 = [[1,0,0],[0,0,1],[0,1,0]]`.
- Printed 180–181 (PDF 13–14), (2.1.1)–(2.1.3): the character of `N` is
  `θ(n) = ∏ ψ(n_(i,i+1))`; the automorphism `g ↦ w g^ι w⁻¹` with the
  signed `w` fixes `N` and `θ`, and for `W` in `W(π; ψ)` the dual
  `W~(g) = W(w g^ι)`, `g^ι = ᵗg⁻¹` (0.4.3), lies in `W(π~; ψ)`, for the
  *same* `ψ`.
- Printed 177 (PDF 10), (1.1.1)–(1.1.2): `Z(Φ, s, f) = ∫ Φ(x) f(x) |det x|^s d×x`
  for matrix coefficients `f`, convergence of `Z(Φ, s + (r-1)/2, f)`, the
  g.c.d. `L(s, π) = 1/Q(q^(-s))`, `Q(0) = 1`, and the functional equation
  with `f^ι(g) = f(ᵗg⁻¹)` and `Φ^(x) = ∫ Φ(y) ψ(Tr(y ᵗx)) dy`. These are the
  conventions of the matrix premise: shift `n/2 = (r-1)/2`, `coefficientIota`,
  plus transpose pairing.
- Printed 181 (PDF 14): for `r = 1` genericity is empty, all quasicharacters
  of `F×` are generic, and the Whittaker model consists of the scalar
  multiples of the character.
- Printed 183 (PDF 16), Remark (2.2.5): spaces of `ψ`-Whittaker functions,
  stable under right translation, finitely generated and admissible.
- Printed 185–187 (PDF 18–20), Proposition (3.1) and its proof: for
  `Φ(ωx) = Φ(x)` on a compact open `Ω`, with Haar probability measure `dω`
  on `Ω`, the average `f(g) = ∫_Ω W(ωg) dω` (3.1.3) is a matrix coefficient
  and `Z(Φ, s, W) = Z(Φ, s, f)` (3.1.4); the functional equation is
  `Z(Φ', 1 - s + (r-1)/2, W~)/L(1-s, π~) = ε(s, π, ψ) Z(Φ, s + (r-1)/2, W)/L(s, π)`
  with `Φ'(g) = Φ^(wg)` and `W~(g) = W(w ᵗg⁻¹)` for the signed `w` of
  (0.4.2), obtained from (1.1.2) by the change of variables `g ↦ wg`.
- Printed 188–190 (PDF 21–23), Section 4.1: the integrals
  `Ψ(s, W; j) = ∫∫ W([a, 0, 0; x, I_j, 0; 0, 0, I_(r-j-1)]) |a|^(s-(r-1)/2) d×a dx`,
  `0 ≤ j ≤ r - 2`, and `Ψ(s, W; j, Φ)`. Remark (4.2) extends the results to
  spaces as in Remark (2.2.5). The block matrix and exponent are those of
  `unequalRankIntegral` with test rank one and `r - j - 1 = k + 1`.
- Printed 190–194 (PDF 23–27): Theorem (4.3) and Lemmas (4.3.1), (4.3.4)
  (compactly supported measures `μ_Φ`, Haar measure of `K_m`).
- Printed 194 (PDF 27), Section 4.4: (4.4.1)
  `Z(Φ', 1 - s + (r-1)/2, W~) = ε'(s, π, ψ) Z(Φ, s + (r-1)/2, W)` is taken as
  the definition of `ε'`. The text then says that if one *assumes* (4.4.1)
  for the space of Remark (4.2), with `ε'` replaced by the appropriate factor,
  Theorem (4.5) holds in that generality. `π(w')W` is the right translate
  `h ↦ W(hw')`.
- Printed 194 (PDF 27), Theorem (4.5): for `j + k = r - 2`, `j, k ≥ 0`,
  `Ψ(1 - s, (π(w')W)~; k) = ε'(s, π, ψ) Ψ(s, W; j)`, and a second identity
  for `Ψ(s, W; j, Φ)`.
- Printed 196 (PDF 29): the remark `(π(w')W)~(g) = W~(gw')`, in the
  source's signed conventions.
- Printed 194–198 (PDF 27–31): proof. Lemmas (4.5.1), (4.5.2) compare the
  matrix integral with `Φ'` and the `μ_Φ`-averaged rank-one integrals; on
  printed 197 the case `j = 0` follows from (3.1) by choosing `Φ` and `μ_Φ`
  as in (4.3.4); printed 197–198 pass from `j` to `j + 1` by Fourier
  inversion with characteristic functions of `𝔓^(-m)` and `𝔓^m`.
- No registered erratum for these passages was found.

Correspondence. The role of `ε'(s, π, ψ)` of (4.4.1), for the model, is
played by the matrix gamma factor `c q^(-a s) P(q^(-s))/PDual(q^(-(1-s)))` of the premise, which is the
displayed `rationalGammaExpression`. With `r = n + 1`, the condition
`j + k = r - 2` is `n = j + k + 1`, which is exactly the range quantified in
`UnequalRankGammaEquation`. The source's transformed side is **not**
definitionally the Lean one. The source uses the signed `w`, `w'` of
(0.4.2) and a dual in the same `ψ`-space (2.1.3); the Lean
`dualUnequalRankModelIntegralAt` uses the unsigned `J_(n+1)` and
`blockWeylAt 0 n`, and `firstDualFunction` is a `ψ⁻¹`-Whittaker function.
The two block-`k` integrals agree only after the explicit sign conversion
below, applied to a right translate of the model vector and to the integration
variables. The source integrals have no second function; here the second
function is a constant model vector of the trivial character, and the
source's `d×a` must be compared with `μ` through the quotient-integration
formula, for every compatible `μ`.

Sign conversion, for `r = n + 1 ≥ 2`, with one-based indices. Let
`J = J_r`, `B = blockWeylAt 0 n = diag(1, J_(r-1))`,
`D = diag(1, -1, 1, ..., (-1)^(r-1))`,
`T = J D J = diag((-1)^(r-1), ..., -1, 1)` and `E = diag(-1, 1, ..., 1)`.
Direct multiplication gives

```text
w = D J = J T,        w' = T E B.
```

The diagonal matrices `D`, `T`, `E` are involutions, `E` commutes with `B`, and
`w`, `w'`, `T` are orthogonal, so `(ThT)^ι = T h^ι T` with
`h^ι = ᵗh⁻¹`. For a model vector `W` put `W_E(h) = W(hE)`, again a vector of
the same right-translation model. Then for every `g`

```text
W_E(w g^ι w') = W(J (T g T)^ι B).
```

The left side is the source's `(π(w')W_E)~(g)`; the right side is the Lean
translated first dual of `W` at `TgT`. Write
`m_l(a, x) = [a, 0, 0; x, I_l, 0; 0, 0, I_(r-l-1)]`. Then

```text
m_l(a, x) E = m_l(-a, -x),     T m_l(a, x) T = m_l(a, S_l x),
S_l = diag(-1, 1, -1, ..., (-1)^l).
```

So the source block-`j` integral of `W_E` is the Lean block-`j` integral of
`W` after `(a, x) ↦ (-a, -x)`, and the source block-`k` integral of
`(π(w')W_E)~` is the Lean transformed block-`k` integral of `W` after
`x ↦ S_k x`. Conjugation by `T` negates every superdiagonal entry, which is
why the source's same-`ψ` dual corresponds to the Lean `ψ⁻¹` dual. These
identities were checked in exact rational arithmetic for `r = 2, ..., 9`
and all blocks; they are an informal derivation, not a Lean proof. An
equivalent route keeps `W` and uses `w g^ι w' = J (-D g E')^ι B` with
`E' = diag(1, 1, -1, 1, ...)`, substituting `(a, x) ↦ (-a, εx)`,
`ε = (1, -1, 1, ...)`, on the transformed side only. At `r = 1` there is no
sign issue (`w = J_1 = 1`), but the source theorem is empty there (see
below).

## Conditional adaptation and provenance

The Lean packaging is internal. It combines the hypothesis form of
Section 4.4 with Remark (4.2), and the Library's predicates; it is not a
transcription of a single numbered result.

- **Premise on the model.** The source assumes the Whittaker-side equation
  (4.4.1) for the function space. The Lean premise instead is the matrix
  equation in the form (1.1.2) for the actual matrix coefficients of the
  right-translation representation on the coefficient model of `ℓ`, with
  `ΦHat`, `coefficientIota` and the same `ν`. A proof must produce (4.4.1)
  for model vectors from this premise: compact averaging (3.1.3)–(3.1.4)
  turns model vectors into actual bi-smooth coefficients of the model, and
  the signed Weyl factors in `Φ'(g) = Φ^(wg)` and `W~(g) = W(w ᵗg⁻¹)`
  require an actual change of variables `g ↦ wg` in the matrix integrals
  (a signed permutation, so `|det w| = 1`) and actual Fourier compatibility
  for the plus transpose pairing with the same `ν`, not a definitional
  identification.
- **Signed-to-unsigned conversion.** The source equation for the
  `n > 0` blocks is in the signed conventions; the Lean conclusion is in
  the unsigned ones. A proof must carry out the sign conversion above (or
  run the argument of (3.1) directly with `J_(n+1)` and `ψ⁻¹`) as actual
  changes of variables. The model contains `W_E` by right-translation
  stability, so no extra hypothesis is needed. The substitutions are
  coordinate sign changes `x ↦ -x`, which preserve the supplied `ν` and
  hence `rectangularMeasure ν j 1` and `rectangularMeasure ν k 1`, and
  `a ↦ -a`, a translation of `GL_1` that preserves `|a|` and Haar measure;
  for an arbitrary compatible quotient measure `μ` this invariance must be
  proved, for instance through the quotient-integration formula and
  triviality of `N₁`. The second functions are constant model vectors of
  the trivial character on both sides, so no character value at `-1`
  appears. Right translation by `E` is absorbed into `W_E`, so no central
  character of the possibly reducible `σ` is used. Hence the conversion
  introduces no scalar, Jacobian or sign factor, and the gamma factor stays
  `rationalGammaExpression (LocalFactor.residueReflection F) c a P PDual`.
- **Hypotheses on the model.** Remark (2.2.5) needs the function space to be
  admissible and finitely generated. The model is a quotient of `σ` through
  the surjective intertwiner `Whittaker.modelMap`, so a proof can transport
  these properties (for instance through
  `Unramified.SphericalExistence.isAdmissible_of_surjective`,
  `Representation.IntertwiningMap.equivLinearMapAsModule` and
  `Module.Finite.of_surjective`). These are proof obligations, not premises.
- **All functionals and measures.** By the one-dimensional functional space,
  every nonzero `ℓ₁` is a nonzero multiple of `ℓ` and has the same
  coefficient model, so one supplied `ℓ` must suffice. The conclusion also
  quantifies over every compatible quotient measure and every nonzero `ℓ'`.
- **All blocks and `ν`.** Theorem (4.5) covers every `j + k = r - 2`. The
  source assumes that `ψ` has exponent zero (printed 193) and passes from
  `j` to `j + 1` with the characteristic functions of `𝔓^(-m)` and `𝔓^m`.
  A proof for the arbitrary `ψ` quantified here must carry out this
  Fourier-inversion step on expanding compact-open lattices `H` and their
  actual `ψ`-annihilators `H⊥`, computing the Fourier transforms and volume
  factors with the supplied self-dual `ν`. The annihilator lattice depends on
  the conductor of `ψ`. Self-duality gives `vol_ν(H) · vol_ν(H⊥) = 1`, and
  the same `ν` must be retained in all rectangular measures and Fourier
  tests.
- **Rank one `n = 0`.** The source's range `0 ≤ j ≤ r - 2` is empty at
  `r = 1`, and Theorem (4.5) says nothing there. The Lean conclusion at
  `n = 0` is the equal-rank `GL_1 × GL_1` equation, which is an internal
  boundary case of this packaging. A proof uses a separate Tate-type
  argument: by printed 181 and full Whittaker type, the model is spanned by
  one smooth character, so model vectors are themselves matrix coefficients;
  `N₁` is trivial and `μ` corresponds to `generalLinearHaar F 0`; `lastRow`
  identifies `F¹` with `1 × 1` matrices, the row Fourier pair with the
  matrix Fourier pair for the same `ν`, and `n/2 = 0`. The positive-rank
  source argument does not prove this case.

## What is not asserted

The statement asserts no existence of matrix data for any representation,
reducible or not; no L-factor or epsilon-factor relation; no comparison of
ideals `I₁ = I₃` or `I₂ = I₃`; no nontrivial quasicharacter twist and no
transport to other `GL_1` carriers; and no multiplicativity. It covers only
the trivial rank-one test.

## Compilation record

`lean_check` in environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` with
modules `GodementJacquet.AnalyticData`, `RankinSelberg.PadicPairFactors`,
`RankinSelberg.PairFactors`, `LocalFactor.ResidueReflection` and this module
(diagnostic `56046e04-3a30-48eb-a23c-4dfbb3a0498d`): no errors or warnings;
the declaration is a definition with `statement_returns_prop: true`, level
parameters `[uF, uV]`, and axioms `propext`, `Classical.choice`,
`Quot.sound` only.
