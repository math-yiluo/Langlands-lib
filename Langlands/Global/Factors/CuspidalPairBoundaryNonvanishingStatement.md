# Nonvanishing of partial cuspidal pair L-functions on the line `Re s = 1`

Author: Worker 3657. Statement contribution to task
`34b81620-20d7-4059-9b08-6bedd1c1c029`, revision 1.

**Scope.** This module states one proposition, uses two auxiliary definitions, and
proves nothing:

- `Langlands.Global.CuspidalPairBoundaryNonvanishing.partialEulerFactor`;
- `Langlands.Global.CuspidalPairBoundaryNonvanishing.IsPartialPairLFunction`;
- `Langlands.Global.CuspidalPairBoundaryNonvanishingStatement`.

The module is `Langlands.Global.Factors.CuspidalPairBoundaryNonvanishingStatement`.
The proposition is Shahidi (1981), Theorem 5.2, for actual cuspidal realizations
with unitary central characters. It says the partial Rankin–Selberg L-function
`L^S(s, π × π')` has no zero on the line `Re s = 1`. The finite-place vocabulary
(`pairEulerPolynomial`, `residueCardinality`, the Satake spectra of a presentation)
is that of the published `CuspidalPairFactorData`. Nothing from that module is
rebuilt.

**Why it is here.** Two published Library modules name this theorem as an
unresolved global input owned by this program:
`Langlands/Global/Factors/AppendixPoleCountingStatement.md` and
`Langlands/Global/Factors/MeromorphicPoleComparisonStatement.md`. Both say that
neither module proves Shahidi (1981), Theorem 5.2, or replaces it with local
conditions.

**Proof target.** A later proof task should prove the Library statement
`Langlands.Global.CuspidalPairBoundaryNonvanishingStatement`. Its universe
parameters are `u` (the number field) and `uQ` (the factor universe of the
spectral presentations).

## 1. Sources

"p." is the printed page and "PDF" the page of the registered file.

| Source ID | Short name | Locators used |
|---|---|---|
| `shahidi-1981-certain-l` | Sh81 | §4 setup p.343 (PDF 48); Thm 4.1 and Example p.344 (PDF 49); §5, Thm 5.1 and proof pp.351–352 (PDF 56–57); Thm 5.2 p.353 (PDF 58) |
| `getz-hahn-2024-automorphic-representations` | GH | Thms 11.6.1–11.6.2 p.308 (PDF 319); (11.23) p.308 (PDF 319); norm shift, convergence and Thm 11.7.1 p.309 (PDF 320) |
| `cogdell-2004-analytic-theory-gln` | Cog04 | Thm 3.3 p.215 (PDF 218); Thm 4.1 p.219 (PDF 222) |

**What the source states.** Sh81 Thm 5.2 (p.353): let `π` and `π'` be irreducible
admissible cuspidal (non-degenerate) representations of `GL_n(A)` and `GL_m(A)`,
with `π = ⊗_v π_v` and `π' = ⊗_v π'_v`. Let `L(s, π_v × π'_v)` be the corresponding
Jacquet–Shalika L-function, and set `L_S(s, π × π') = ∏_{v ∉ S} L(s, π_v × π'_v)`.
Then `L_S(1 + it, π × π')` is nonzero for every real `t`. The proof applies
Thm 5.1 to `G = GL_(n+m)` with Levi subgroup `GL_n × GL_m`.

The hypotheses come from the surrounding text:

- **`S`.** Thm 5.1 (p.351) takes `S` to be a finite set of places that contains
  the infinite places, such that at every `v ∉ S` both the cuspidal
  representation of the Levi subgroup (here `π_v ⊗ π'_v`) and the component
  `χ_v` of the generic character of the unipotent radical are unramified.
- **Unitarity.** The §4 setup (p.343) writes the cuspidal representation as
  `⊗_v π_v` with every `π_v` irreducible and unitary.
- **Archimedean condition.** Thm 5.1 also assumes that `π_v` is "fine" at every
  archimedean place. The Example after Thm 4.1 (p.344) observes that this holds
  for `GL_n × GL_m` because the components are unitary.

**Meaning of "nonzero".** `L_S` is meromorphic and has a pole at `s = 1` when
`π' ≅ π̃` (GH Thm 11.7.1, p.309). "Nonzero" therefore means "has no zero": at
`1 + it`, `L_S` either has a pole or is analytic with a nonzero value.

**Supporting facts.** These are used only in the existence conjunct and in the
normalizations below.

- GH (11.23) (p.308) defines the global L-function as the Euler product for
  `Re s` large.
- GH p.309 shows that, for representations trivial on `A_GL`, the product
  converges absolutely for `Re s > 1`, and states the norm shift
  `L(s, π|det|^(s₁) × π'|det|^(s₂)) = L(s + s₁ + s₂, π × π')`.
- GH Thm 11.7.1 (p.309) and Cog04 Thm 4.1 (p.219) give the meromorphic
  continuation.
- Cog04 Thm 3.3 (p.215) and GH Thms 11.6.1–11.6.2 (p.308) give the unramified
  factor `det(I - q^(-s) A ⊗ A')^(-1)`.

## 2. Declarations

Namespace `Langlands.Global.CuspidalPairBoundaryNonvanishing`. The field `F` is a
number field with `[CompactSpace (AdeleQuotient F)]`, the instance needed by
`CuspidalOperatorRealization`.

### `partialEulerFactor P P' hP hP' v s`

The inputs are presentations `P`, `P'` of cuspidal realizations `T`, `T'` of
`GL_(r+1)` and `GL_(t+1)`, a finite set `S` of finite places with
`hP : P.exceptional ⊆ S` and `hP' : P'.exceptional ⊆ S`, a place
`v : {v : FinitePlace F // v ∉ S}`, and `s : ℂ`. The value is

`((pairEulerPolynomial a b).eval (q_v^(-s)))⁻¹ = ∏_(i,j) (1 - a_i b_j q_v^(-s))⁻¹`.

Here `a = P.spectralSystem.eigenvalues v _` and
`b = P'.spectralSystem.eigenvalues v _`. The proofs that `v` lies outside the two
exceptional sets come from `hP` and `hP'`. Also `q_v = residueCardinality v`, and
`q_v^(-s)` is `RankinSelberg.spectralPoint q_v s`. This is the unramified factor
`L(s, π_v × π'_v)` of Sh81 Thm 5.2, in the form of Cog04 Thm 3.3 and GH
Thms 11.6.1–11.6.2.

### `IsPartialPairLFunction P P' hP hP' L`

For `L : ℂ → ℂ`, both of the following hold:

1. `L` is meromorphic on all of `ℂ` (`MeromorphicOn L Set.univ`);
2. for some real `σ` and every `s` with `σ < Re s`, the sum
   `∑_(v ∉ S) ‖partialEulerFactor … v s - 1‖` converges and the Euler product over
   the finite places outside `S` has value `L s` (`HasProd`).

The convergence clause has the same form as `CompletedEquationHolds` in
`CuspidalPairFactorData`: absolute convergence on *some* right half-plane. Two such
functions agree on a right half-plane. Both are meromorphic on the connected set
`ℂ`, so by the identity theorem they agree off a discrete set and have the same
`meromorphicOrderAt` at every point. The predicate therefore determines the
partial L-function up to values at isolated points. It does not determine those
values, and `meromorphicOrderAt` ignores them.

### `CuspidalPairBoundaryNonvanishingStatement`

The hypotheses are:

- a number field `F`;
- ranks `r`, `t`;
- actual cuspidal realizations `T : CuspidalOperatorRealization F r` and
  `T' : CuspidalOperatorRealization F t`, both with
  `HasUnitaryCentralCharacter`;
- spectral presentations `P`, `P'` of `T` and `T'`;
- a finite set `S` of finite places containing `P.exceptional` and
  `P'.exceptional`.

The conclusion has two conjuncts:

1. **existence:** some `L : ℂ → ℂ` satisfies `IsPartialPairLFunction P P' hP hP' L`;
2. **nonvanishing:** every such `L` satisfies
   `meromorphicOrderAt L (1 + y * I) ≤ 0` for every real `y`.

Mathlib's order convention is the following. Zeros have positive order and poles
negative order. `⊤` is the order of a function that vanishes identically near the
point. So `≤ 0` excludes a zero and also excludes vanishing near the point. It
allows a pole, as at `s = 1` when `π' ≅ π̃`.

## 3. Hypotheses and their match with the source

- **Cuspidal realizations.** `CuspidalOperatorRealization` is an actual
  irreducible cuspidal subspace of automorphic forms on `GL_(r+1)`, and `r + 1`,
  `t + 1` are Shahidi's `n`, `m` (both at least 1). Sh81 also assumes
  "non-degenerate". For cuspidal representations of `GL_n` this is automatic,
  since they have Whittaker models (Shalika 1974, Sh81's reference [27]). In the
  Library the corresponding input is the published, unproved
  `Langlands.Global.WhittakerExpansionStatement`. It is not a hypothesis here;
  any use of it belongs to the proof.
- **Unitarity.** Sh81 assumes unitary local components (p.343). Here the
  hypothesis is `HasUnitaryCentralCharacter T`: some continuous character of the
  idele class group with values of norm 1 is the central character of `T`. This
  is the convention of the published `CuspidalUnitaryLocalUnitarityStatement`.
  The Library proves that it makes the global realization unitarizable
  (`CuspidalOperatorRealization.isUnitarizable_of_hasUnitaryCentralCharacter`,
  module `Langlands.Automorphic.CuspidalUnitaryForm`). Local unitarity of the
  components is the separate statement `CuspidalUnitaryLocalUnitarityStatement`.
  The hypothesis cannot be dropped. Every cuspidal realization is a unitary one
  twisted by `|det|^x`, and by the norm shift (GH p.309) such a twist moves the
  line `Re s = 1` to `Re s = 1 - x`.
- **The set `S`.** Here `S` is any finite set of *finite* places containing both
  exceptional sets. Infinite places never enter the finite Euler product. Outside
  `P.exceptional`, the presentation supplies a nonzero spherical fixed space and
  its Satake spectrum (`HasSphericalHeckeSpectrum`, module
  `Langlands.Automorphic.LocalSphericalHecke`). So both components are
  unramified at every place outside `S`. Sh81 also requires `χ_v` unramified
  outside its set. This does not narrow the statement. Let `S₀` be `S` together
  with the finitely many finite places where `χ` ramifies. Sh81 applies to `S₀`
  and the infinite places. Then `L^S` is `L^(S₀)` times the finitely many
  factors `L(s, π_v × π'_v)` with `v ∈ S₀ \ S`. Each of these is the inverse of a
  polynomial in `q_v^(-s)`, so it has nonpositive order everywhere. Removing
  places from `S` therefore cannot create a zero.
- **"Fine" at archimedean places.** This is not a hypothesis here. By the Sh81
  Example (p.344) it follows from unitarity for `GL_n × GL_m`.

## 4. Normalizations

- **Satake parameters.** `HasSphericalHeckeSpectrum a` makes the `i`-th standard
  spherical Hecke operator act by `q^(i(n-i)/2) e_i(a)`, the unitary Satake
  normalization. `CuspidalPairFactorData.md` §4 records this, after Gross (1998).
  So `pairEulerPolynomial a b` at `q_v^(-s)` is Cog04's
  `det(I - q_v^(-s) A_π ⊗ A_π')`. With this normalization the unramified factor
  is the Jacquet–Shalika factor of Sh81 Thm 5.2, and the boundary line is
  `Re s = 1`, matching GH p.309 (absolute convergence for `Re s > 1`).
- **Robustness to inverting the parameters.** For unitary `π`, `π̃ ≅ π̄`. The
  parameters `a⁻¹` give `L^S(s, π̃ × π̃') = conj(L^S(conj s, π × π'))`. So
  nonvanishing at every `1 + iy` holds for one convention exactly when it holds
  for the other. The statement does not depend on this choice.
- **Convergence region.** The statement asserts absolute convergence only on
  some right half-plane, like `CompletedEquationHolds`. The sharp region
  `Re s > 1` (GH p.309) is not stated.

## 5. Content beyond Sh81 Theorem 5.2, and provenance

- **Existence.** The first conjunct asserts that `L^S` continues meromorphically
  to `ℂ`. Sh81 does not prove this at Thm 5.2. For the meromorphy of `L_S` it
  cites Langlands, *Euler products* (p.344, its reference [15]), and the theorem
  is stated for that meromorphic function. The conjunct makes the statement
  non-vacuous. It follows from GH Thm 11.7.1 or Cog04 Thm 4.1 by dividing the
  completed L-function by the archimedean factors and by the finitely many
  finite local factors at places in `S`. The published
  `CuspidalPairGlobalFunctionalEquationStatement` gives the continuation only for
  the completed function. This module does not import or use it.
- **Universal second conjunct.** Sh81 speaks of "the" function `L_S`. By the
  uniqueness remark in §2, quantifying over every `L` with
  `IsPartialPairLFunction` adds no mathematical content. It saves consumers the
  identity-theorem argument when they hold their own representative.
- **Not included.** The statement says nothing about holomorphy on `Re s = 1`,
  pole locations, boundedness in vertical strips, or zeros off the line.
  `HolomorphicUnitAt` in `MeromorphicPoleComparisonStatement` needs holomorphy
  as well as nonvanishing. At points where the partial L-function has no pole,
  that holomorphy is pole information of the kind in GH Thm 11.7.1. It is not
  part of this statement.

## 6. Proof routes (for the proof task)

Sh81 proves Thm 5.1 (pp.351–352) as follows. The non-constant Fourier
coefficient of a cuspidal Eisenstein series on `GL_(n+m)`, induced from `π ⊗ π'`,
factors over places. By the Casselman–Shalika formula, the unramified local
factors are `L(1 + s, π_v × π'_v)⁻¹`. The local Whittaker values at places in
`S` can be chosen nonzero. Therefore zeros of `L_S(1 + s)` are poles of the
Eisenstein series, and the Eisenstein series is holomorphic on the unitary
axis. This needs:

- Langlands' theory of Eisenstein series, with holomorphy on the unitary axis;
- the Casselman–Shalika formula (Sh81's reference [3]);
- the local theory of Sh81 §3.

None of these is in the Library. The proof task may choose another established
route, and it must record the route it uses.
