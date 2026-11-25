# Totally complex form of the poles of completed cuspidal pair L-functions

It extends to the Harris branch the restriction of the global statements on the
route to the local correspondence to totally complex base fields
(`CuspidalPairFunctionalEquationTCStatement.md` §4).

**Scope.** The module `Langlands.Global.Factors.CuspidalPairPoleTCStatement`
defines one proposition, `Langlands.Global.CuspidalPairPoleTCStatement.{u, uQ}`,
and proves nothing. It is the published
`Langlands.Global.CuspidalPairPoleStatement.{u, uQ}` (module
`Langlands.Global.Factors.CuspidalPairPoleStatement`) with one more instance
argument, `[NumberField.IsTotallyComplex F]`, inserted directly after
`[NumberField F]`. The universe parameters are the same, and the rest of the body
is copied verbatim.

## 1. The statement

All vocabulary is that of the original, and nothing is redefined:
`IsTrivialOnSplitCentre`, `FinitePairLChoice`, `IsCompletedLFunction`,
`HasSimplePoleProfile` and `IsBoundedInVerticalStrips` are the auxiliary
definitions of `CuspidalPairPoleStatement.lean`, explained in
`CuspidalPairPoleStatement.md` §2. In words:

For every totally complex number field `F : Type u` with
`[CompactSpace (AdeleQuotient F)]`, all `r t : ℕ` and actual cuspidal realizations
`T` of `GL_(r+1)` and `T'` of `GL_(t+1)` over `F` that are trivial on the split
centre `A_GL`, and all spectral presentations `P`, `P'` (universes `u`, `uQ`) with
irreducible admissible components:

1. the local data exist: a finite pair L-factor choice, a real-place parameter of
   `T` and of `T'` at every real place, and a complex-place parameter of each at
   every complex place; and
2. for every finite choice `c` and every choice of archimedean parameters `dR`,
   `dR'` (real places) and `dC`, `dC'` (complex places) of `T` and `T'`, there is a
   function `Λ : ℂ → ℂ` that is the completed L-function of `c` with archimedean
   factor `infiniteL` (the product of the inverse denominators of the archimedean
   pair L-factors). `Λ` is holomorphic off `{0, 1}`, has at most simple poles at
   `s = 0` and `s = 1`, and has poles there exactly when `r = t` and `T'` is the
   contragredient of `T`; and `Λ` is bounded on every vertical strip outside
   every pair of small discs around `0` and `1`.

## 2. Effect of the restriction

Mathlib's `NumberField.IsTotallyComplex F` says that every infinite place of `F` is
complex (`Mathlib/NumberTheory/NumberField/InfinitePlace/TotallyRealComplex.lean`).
So the subtype `{v : InfinitePlace F // v.IsReal}` is empty, and:

- the real-place clause of the existence part holds vacuously;
- the quantified real-place parameters `dR`, `dR'` are functions on an empty type,
  their hypotheses hold vacuously, and the product over real places in
  `infiniteL` is an empty product, equal to `1`.

The body keeps these clauses verbatim, so that
the new proposition differs from its original only by the instance argument. The
complex places remain: a proof still needs the `GL_n(ℂ)` archimedean theory (the
pair factors of Jacquet (2009) at complex places), but not the `GL_n(ℝ)` theory.

## 3. Relation to the original

The original implies the totally complex form at the same universe levels: apply
it to the same field and forget the new instance. A development check compiled
this implication as `fun h F _ _ _ _ => h F`. The converse is
not claimed. The statement makes no claim about number fields with a real place.

## 4. Why the totally complex form is stated

In the Library's route to the local correspondence (route note
`notes/henniart/llc-proof-route.md`), `CuspidalPairPoleStatement` is used for the
Jacquet–Shalika rigidity of Harris's input 9
(`Langlands.Automorphic.Unramified.CuspidalSpectralRigidityStatement`): the proof
of Jacquet–Shalika (1981), Theorem 4.2, compares the poles at `s = 1` of pair
L-functions over the same number field. Harris's Proposition 4.8 applies its
inputs only over the CM fields of a `Proposition48Problem` and their finite
extensions. A CM field is totally complex (Mathlib
`NumberField.IsCMField.isTotallyComplex`), and every finite extension of a totally
complex field is totally complex (`NumberField.isTotallyComplex_of_algebra`). So
on the route the pole statement is needed only over totally complex fields, and
this form, together with the totally complex rigidity of
`CuspidalSpectralRigidityTCStatement.md`, removes the real-place (`GL_n(ℝ)`)
archimedean theory from the Harris branch.

The unrestricted statement stays in the Library as infrastructure.

## 5. Sources and provenance

Provenance: *derived*. The proposition is the special case, for totally complex
base fields, of the published statement, which follows the sources below; they
state the result for every number field. The sources and locators are those of
the original; the full correspondence, the hypotheses, the normalizations and the
content beyond the sources are in `CuspidalPairPoleStatement.md` §§1 and 3–5, and
its proof routes in §6.

- `getz-hahn-2024-automorphic-representations` (GH): Theorem 11.7.1, printed
  p.309 (PDF 320), for the completed function `Λ(s, π × π')` of (11.23)–(11.24),
  p.308 (PDF 319); `A_GL` from (2.20), p.68 (PDF 85).
- `cogdell-2004-analytic-theory-gln` (Cog04): Theorem 4.1, printed p.219
  (PDF 222), item 2 (bounded in vertical strips away from the poles; pp.220–221,
  PDF 223–224), and Theorem 4.2, printed p.222 (PDF 225), the poles.
