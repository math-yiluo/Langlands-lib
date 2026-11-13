# The pole order at `s = 1` of `L(s, π₀ × (π₁ ⊞ ⋯ ⊞ π_k))`

Author: Worker 3657. Statement contribution to task
`34b81620-20d7-4059-9b08-6bedd1c1c029`, revision 1.

**Scope.** This module states one proposition, uses two auxiliary
definitions, and proves nothing:

- `Langlands.Global.CuspidalIsobaricPoles.HasPoleOrder`;
- `Langlands.Global.CuspidalIsobaricPoles.contragredientMultiplicity`;
- `Langlands.Global.CuspidalIsobaricPoleOrderStatement`.

The module is `Langlands.Global.Factors.CuspidalIsobaricPoleOrderStatement`.
The proposition is Getz–Hahn (2024), Lemma 11.8.1. Let `π₀, π₁, …, π_k` be
cuspidal representations trivial on `A_GL`. Then the order of the pole at
`s = 1` of `L(s, π₀ × (⊞_(i=1)^k π_i))` is the number of `i ≥ 1` with
`π_i ≅ π₀^∨`. By Getz–Hahn's convention this L-function is the product of the
completed pair L-functions `Λ(s, π₀ × π_i)`.

All vocabulary for the pair L-functions is reused from the Library module
`Langlands.Global.Factors.CuspidalPairPoleStatement`: `IsTrivialOnSplitCentre`,
`FinitePairLChoice` and `FinitePairLChoice.IsCompletedLFunction`. The
archimedean factor is the one of that statement. Nothing from it is rebuilt.

**Why it is here.** The program ledger
`notes/automorphic/global-program-coverage.md` (section "13 November 2026
carry-over") lists GH Lemma 11.8.1 as an L4 target of this program with no
public statement. The ledger records its hypotheses: each `π_i` is cuspidal
and trivial on the split centre of its own group.

**Proof target.** A later proof task should prove the Library statement
`Langlands.Global.CuspidalIsobaricPoleOrderStatement`. Its universe
parameters are `u` (the number field) and `uQ` (the factor universe of the
spectral presentations).

## 1. Sources

"p." is the printed page and "PDF" the one-based page of the registered file.

| Source ID | Short name | Locators used |
|---|---|---|
| `getz-hahn-2024-automorphic-representations` | GH | Thm 11.7.1, p.309 (PDF 320); §11.8, local isobaric convention pp.311–312 (PDF 322–323); global convention, multiplicity and Lemma 11.8.1, p.312 (PDF 323) |

**What the source states.** GH §11.8 (pp.311–312) first defines, for local
irreducible admissible `π ≅ ⊞_(i=1)^k π_i` and `π' ≅ ⊞_(j=1)^(k') π'_j` with
essentially square-integrable `π_i`, `π'_j`,
`L(s, π × π') = ∏_(i=1)^k ∏_(j=1)^(k') L(s, π_i × π'_j)`. It then says (p.312):
"We adopt the analogous conventions in the global case and thereby obtain
global Rankin–Selberg L-functions and ε-factors for isobaric automorphic
representations." So `L(s, π₀ × (⊞_(i=1)^k π_i)) = ∏_(i=1)^k L(s, π₀ × π_i)`.

GH p.312 continues: "Let `π₀, π₁, …, π_k` be a collection of cuspidal
automorphic representations of `A_(GL_(n_i)) \ GL_(n_i)(𝔸_F)`. The
multiplicity of `π₀` in `⊞_(i=1)^k π_k` is `|{1 ≤ i ≤ k : π_i ≅ π₀}|`." (The
subscript `k` of `π_k` under the isobaric sum is a misprint for `i`.) Then:

> **Lemma 11.8.1** Assume that `π₀, π₁, …, π_k` are a collection of cuspidal
> automorphic representations of `A_(GL_(n_i)) \ GL_(n_i)(𝔸_F)`. The order of
> the pole of `L(s, π₀ × (⊞_(i=1)^k π_i))` at `s = 1` is the multiplicity of
> `π₀^∨` in `⊞_(i=1)^k π_i`.

GH gives no proof beyond "Applying Theorem 11.7.1 we deduce". The global
Rankin–Selberg L-function of GH is the completed one, with the archimedean
factors (GH (11.23), p.308, and Thm 11.7.1, p.309).

## 2. Declarations

Namespace `Langlands.Global.CuspidalIsobaricPoles`.

### `HasPoleOrder f s m`

For `f : ℂ → ℂ`, `s : ℂ` and `m : ℕ`:
`min (meromorphicOrderAt f s) 0 = -m` in `WithTop ℤ`.

Mathlib's order convention: zeros have positive order, poles negative order,
and `⊤` is the order of a function that vanishes identically near `s`. So
`min (ord_s f) 0` is minus the order of the pole of `f` at `s`, and it is `0`
when `f` has no pole there. The predicate says that the order of the pole of
`f` at `s` is `m`, with "order `0`" meaning "no pole". For `m ≥ 1` it says
exactly `meromorphicOrderAt f s = -m`. For `m = 0` it says
`0 ≤ meromorphicOrderAt f s`, so it allows a zero. The predicate does not
itself assume that `f` is meromorphic at `s`. In the statement every factor
is meromorphic on `ℂ`.

### `contragredientMultiplicity T₀ T`

For an actual cuspidal realization `T₀` of `GL_(r₀+1)` and a family
`T : (i : Fin k) → CuspidalOperatorRealization F (r i)`: the cardinality
(`Nat.card`) of the set of indices `i` for which some `hr : r₀ = r i` exists
with `IsContragredientOf (T i).realization (hr ▸ T₀.realization)`.
`IsContragredientOf T S` says that `T` realizes the contragredient of `S`. So
this is `|{1 ≤ i ≤ k : π_i ≅ π₀^∨}|`, GH's multiplicity of `π₀^∨` in
`⊞ π_i`, with GH's indices `1, …, k` renumbered as `0, …, k - 1`. The rank
condition `r₀ = r i` is part of `π_i ≅ π₀^∨`.

### `CuspidalIsobaricPoleOrderStatement`

The hypotheses are:

- a number field `F` with `[CompactSpace (AdeleQuotient F)]`, the instance
  needed by `CuspidalOperatorRealization`;
- an actual cuspidal realization `T₀` of `GL_(r₀+1)`, a natural number `k`, and
  actual cuspidal realizations `T i` of `GL_(r i + 1)` for `i : Fin k`, all with
  `IsTrivialOnSplitCentre`;
- spectral presentations `P₀` of `T₀` and `P i` of `T i`, with irreducible
  admissible finite local components (`h₀`, `h i`).

The conclusion has three conjuncts.

1. **Existence of the data.** For every `i`, `FinitePairLChoice P₀ (P i) h₀ (h i)`
   is nonempty. At every real (complex) place, `T₀` and every `T i` have a
   real (complex) standard-module parameter.
2. **Existence of the pair L-functions.** Fix any choices: `c i` of finite
   pair L-data for every `i`, parameter families `dR₀`, `dR i` at the real
   places and `dC₀`, `dC i` at the complex places of `T₀` and `T i`. Put

   `L∞,i(s) = ∏_(v real) (realPairLFactor (dR₀ v) (dR i v)).denominator(s)⁻¹ ·
   ∏_(v complex) (complexPairLFactor (dC₀ v) (dC i v)).denominator(s)⁻¹`,

   the archimedean factor of `CuspidalPairPoleStatement` for the pair
   `(T₀, T i)`. Call `Λ` a pair L-function for `i` if `Λ` is meromorphic on
   `ℂ` (`MeromorphicOn Λ Set.univ`) and `(c i).IsCompletedLFunction L∞,i Λ`. The
   second condition says that, on some right half-plane, the finite Euler product
   of `c i` converges absolutely and `Λ` is `L∞,i` times it. The conjunct
   asserts that there is a family `Λ : Fin k → ℂ → ℂ` with `Λ i` a pair
   L-function for `i` for every `i`.
3. **The pole order.** For every such family `Λ`,
   `HasPoleOrder (fun s => ∏ i, Λ i s) 1 (contragredientMultiplicity T₀ T)`.

The function `s ↦ ∏_i Λ i s` is GH's `L(s, π₀ × (⊞_(i=1)^k π_i))`. When `k = 0`
it is the constant `1`, with no pole, and the multiplicity is `0`.

**Uniqueness of the pair L-functions.** Two meromorphic functions on `ℂ` that
agree on a right half-plane agree off a discrete set, by the identity theorem.
Their meromorphic orders then agree at every point. So conjunct 3 is about the
L-function itself and does not depend on the representative `Λ i`. Requiring
meromorphy on all of `ℂ` is what makes `Λ i` unique in this sense. Conjunct 2
makes conjunct 3 non-vacuous.

## 3. Hypotheses and their match with the source

- **Cuspidal realizations.** `CuspidalOperatorRealization F r` is an actual
  irreducible cuspidal subspace of automorphic forms on `GL_(r+1)`. `r₀ + 1` and
  `r i + 1` are GH's `n₀` and `n_i`.
- **Trivial on `A_GL`.** GH's `A_(GL_(n_i)) \ GL_(n_i)(𝔸_F)` says that `π_i` is
  trivial on the split component `A_(GL_(n_i))` of the centre of its own group.
  This is stated by `IsTrivialOnSplitCentre`, as in `CuspidalPairPoleStatement.md`
  §2. It cannot be dropped. For `F = ℚ`, `π₀ = 1` and the single constituent
  `π₁ = |·|^(-1)` of `GL_1`, the L-function is `Λ_ℚ(s - 1)`. It has a simple pole
  at `s = 1`, but `π₁ ≇ π₀^∨`.
- **Direction of the contragredient.** GH counts `π_i ≅ π₀^∨`, so the condition
  is `IsContragredientOf (T i) T₀`: `T i` realizes the contragredient of `T₀`.
  The pole condition of `CuspidalPairPoleStatement` for the pair `(T₀, T i)` is
  in the other direction, `IsContragredientOf T₀ (T i)`; see §6.
- **The isobaric sum.** It is not constructed. GH defines its L-function as the
  product of the pair L-functions (§1), and the statement uses that product. The
  multiplicity is GH's count of indices, which needs no isobaric representation.

## 4. Normalizations

The finite and archimedean factors, the variable `s` and the region of
convergence are those of `CuspidalPairPoleStatement.md` §4. They are the
completed Rankin–Selberg L-functions of GH (11.23) and Thm 11.7.1.

## 5. Content beyond the source, and provenance

- **Existence conjuncts.** Conjuncts 1 and 2 assert that the data and the pair
  L-functions exist, so that conjunct 3 is not vacuous. Conjunct 1 is
  conjunct 1 of `CuspidalPairPoleStatement` for each pair `(T₀, T i)`.
  Conjunct 2 follows from conjunct 2 of that statement, which gives a `Λ`
  holomorphic off `{0, 1}` and meromorphic at `0` and `1`.
- **Universal over choices.** GH speaks of "the" L-function. The local
  L-factors do not depend on the choices (`CuspidalPairPoleStatement.md` §2), and
  the pole order does not depend on the representative `Λ i` (§2 above). So
  quantifying over every choice adds no mathematical content.
- **"Order of the pole".** `HasPoleOrder` is the literal reading: the pole order
  is `m`, and "order `0`" means that there is no pole. It does not say whether
  the product vanishes at `s = 1` when the multiplicity is `0`.
- **Not included.** Isobaric representations themselves, the pole at `s = 0`,
  other points of `Re s = 1`, and the analytic properties of the product beyond
  its pole order at `1`.

## 6. Proof routes (for the proof task)

GH's "applying Theorem 11.7.1" does not suffice alone. The order of the pole of
the product is `-min(Σ_i ord_1 Λ i, 0)`. Thm 11.7.1 gives `ord_1 Λ i = -1` when
`π_i ≅ π₀^∨` and `ord_1 Λ i ≥ 0` otherwise. A zero of some other `Λ i` at `1`
would lower the pole order. So the proof also needs `Λ(1, π₀ × π_i) ≠ 0` when
`π_i ≇ π₀^∨`. One route through public Library statements, none of them proved:

1. `CuspidalPairPoleStatement` for each pair `(T₀, T i)` gives
   `-1 ≤ ord_1 Λ i`, with `ord_1 Λ i < 0` exactly when
   `IsContragredientOf T₀ (T i)` (after the rank cast).
2. `IsContragredientOf T₀ (T i)` and `IsContragredientOf (T i) T₀` are
   equivalent for admissible irreducible realizations: the contragredient of the
   contragredient of an admissible representation is the representation itself.
   The Library has no such lemma for `OperatorRealization`, so it would have to
   be proved.
3. `ord_1 Λ i ≤ 0`. Write `Λ i` as `L∞,i · ∏_(v ∈ S) L_v · L^S` with `S` a finite
   set of finite places containing the exceptional sets. `L∞,i` is a product of
   reciprocals of Gamma-type denominators and has no zeros. Each `L_v = 1 / P_v`
   has no zeros. `L^S` has nonpositive order at `s = 1` by Shahidi (1981),
   Theorem 5.2, published as the unproved
   `Langlands.Global.CuspidalPairBoundaryNonvanishingStatement`. Its hypothesis
   of unitary central characters follows from triviality on `A_GL`
   (`CuspidalPairPoleStatement.md` §3).
4. `meromorphicOrderAt` is additive on products of meromorphic functions.
   Hence `ord_1 ∏_i Λ i = -(contragredientMultiplicity T₀ T)`, which implies
   `HasPoleOrder`.

The proof task may choose another established route, and it must record the
route it uses.
