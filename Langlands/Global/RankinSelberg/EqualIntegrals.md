# The equal-rank global Rankin–Selberg integrals

This module defines the objects of the global Rankin–Selberg theory for a pair of cusp
forms on `GL_n × GL_n`, following J. W. Cogdell, *Analytic theory of L-functions for
GL_n* (2004), §2.3, printed pp.208–209 (PDF pp.211–212), registered as
`cogdell-2004-analytic-theory-gln`. These are: the Eisenstein series `E(g, Φ; s, η)`
built from the mirabolic subgroup, the global integral `I(s; φ, φ', Φ)`, and the global
Whittaker integral `Ψ(s; W, W', Φ)`. For the convergence and the analytic properties of
the series, Cogdell refers to H. Jacquet and J. A. Shalika, *On Euler products and the
classification of automorphic representations* (Amer. J. Math. 103, 1981), his reference
[25], Section 4 (p.209).

All declarations are concrete definitions, except one measurability lemma. The module
asserts no analytic property. The analytic theory, the unfolding and the Euler
factorization are separate statement modules.

`F` is a number field and `n = r + 1 ≥ 1`. All declarations are in the namespace
`Langlands.Global.RankinSelbergGlobal`. The module reuses the Library's names from
`Langlands.Global.RankinSelberg.UnequalIntegrals` and
`Langlands.Global.RankinSelberg.WhittakerIntegrals`. `Points F n` is `GL_n(𝔸)`, the
adelic points of the group scheme `Scheme F n = GL_n`. `RationalGL F n` is `GL_n(F)`.
`detNorm F n g` is `|det g|` and `detPower F n g s` is `|det g|^s`. `WhittakerQuotient F n`
is `N_n(𝔸) \ GL_n(𝔸)` and `whittakerQuotientMeasure F n` is its measure. The row vectors
`RowVector F n = 𝔸^n` come from `Langlands.Global.RankinSelberg.SchwartzBruhat`.

**Name of the character.** Cogdell calls the idele class character `η`. Under
`open scoped CategoryTheory.MonObj`, which the module needs for the group structure on
the points of the group scheme, `η` is a reserved token. The Lean argument is therefore
named `χ`. Its type is `IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ`, the continuous characters of
`F^× \ 𝔸^×`. `Automorphic.centralIdeleCharacter F χ` is the same character on the ideles
`𝔸^×`.

The two local instances `equalSchemeAffine` and `equalSchemeSmooth` repeat the Library's
facts that `GL_n` is affine and smooth. The Library's adelic points need them; they are
`local` and change nothing outside the module.

## Elementary maps

* `rationalPoint F n γ` is the point `γ ∈ GL_n(F) ⊆ GL_n(𝔸)` of a rational matrix `γ`.
  It is the Library's principal-point map `AdelicGroupPoints.rational` applied through
  `GeneralLinearGroupPoints.rationalEquiv`.
* `ideleOf F z` is the idele `a = det z` of a point `z ∈ GL_1(𝔸)`. So `GL_1(𝔸)` plays the
  role of `𝔸^×`.
* `lastRow F r g` is the last row `e_n g` of `g ∈ GL_n(𝔸)`, with
  `e_n = (0, …, 0, 1)`.

## The measure `d^×a` on `𝔸^×`

* `determinantSlab F n a b` is the set of classes in `GL_n(F) \ GL_n(𝔸)` of points `g`
  with `a ≤ |det g| < b`. It is the image of that set of points under the quotient map.
  The determinant norm is invariant under `GL_n(F)` by the product formula, so it is a
  union of whole classes; the definition does not need this.
* `ideleSlabVolume F` is the volume of `F^× \ {a ∈ 𝔸^× : 1 ≤ |a| < e}`, that is, of
  `determinantSlab F 1 1 e`, for the Library's quotient Haar measure
  `AdelicGroupPoints.rationalQuotientHaarMeasure F (Scheme F 1)` on `GL_1(F) \ GL_1(𝔸)`.
* `ideleMeasure F` is `(ideleSlabVolume F)⁻¹` times Mathlib's Haar measure on
  `GL_1(𝔸)`.

Cogdell writes `d^×a` and does not fix its normalization. The choice here gives the slab
`F^× \ {1 ≤ |a| < e}` volume one. Writing `𝔸^× = 𝔸^1 × ℝ_(>0)` with the measure
`d^1a · dt/t`, this is the normalization in which `F^× \ 𝔸^1` has volume one, since
`∫_1^e dt/t = 1`. The slab volume is finite and nonzero because `F^× \ 𝔸^1` is compact
and the slab contains a nonempty open set; the definition does not depend on this.

## The section and the Eisenstein series

* `eisensteinSectionIntegrand F χ Φ s g z` is `Φ(a e_n g) |a|^(ns) χ(a)` at `a = det z`.
  The power `|a|^(ns)` is `detPower F 1 z (n s)`.
* `eisensteinSection F χ Φ s g` is Cogdell's

  `F(g, Φ; s, η) = |det g|^s ∫_(𝔸^×) Φ(a e_n g) |a|^(ns) η(a) d^×a`

  (p.208), with `d^×a = ideleMeasure F`.
* `eisensteinParabolic F r` is the rational parabolic `P'_n(F) = Z_n(F) P_n(F)` of type
  `(n - 1, 1)` (p.208). It is the join of the Library's mirabolic subgroup
  `GeneralLinear.mirabolic r F` (last row `(0, …, 0, 1)`) and the center of `GL_n(F)`.
  The center normalizes the mirabolic, so the join is the set of products `z p`, the
  invertible matrices with last row `(0, …, 0, d)`.
* `eisensteinSeries F χ Φ s g` is Cogdell's

  `E(g, Φ; s, η) = Σ_(γ ∈ P'_n(F) \ GL_n(F)) F(γ g, Φ; s, η)`

  (p.208). The sum runs over the Library's `LeftCosetSpace (eisensteinParabolic F r)`,
  whose classes are the cosets `P'_n(F) γ`. Each class `q` contributes the section at
  `rationalPoint (q.out) * g` for the representative `q.out` chosen by `Quotient.out`.
  The section is left `P'_n(F)`-invariant when `χ` is trivial on `F^×` (`|det p| = 1` and
  `e_n p g = d e_n g` for `p ∈ P'_n(F)`), so the term does not depend on the representative;
  the definition does not use this. The sum is Mathlib's `tsum`, which is `0` when the
  family is not summable. Cogdell proves absolute convergence for `Re s > 1` (p.208) for
  unitary `η`. The statements that use the series assert the convergence they need.

## The quotient `Z_n(𝔸) GL_n(F) \ GL_n(𝔸)` and its measure

* `centralRationalSubgroup F n` is the subgroup `Z_n(𝔸) GL_n(F)` of `GL_n(𝔸)`, the join
  of the center of `GL_n(𝔸)` and the Library's rational subgroup.
* `CentralQuotient F n` is `Z_n(𝔸) GL_n(F) \ GL_n(𝔸)`, a `LeftCosetSpace` with its
  quotient σ-algebra.
* `toCentralQuotient F n` is the projection
  `GL_n(F) \ GL_n(𝔸) → Z_n(𝔸) GL_n(F) \ GL_n(𝔸)`, and `measurable_toCentralQuotient`
  proves that it is measurable (from the measurability of the quotient map, by Mathlib's
  `measurable_from_quotient`).
* `centralQuotientMeasure F n` is the image under this projection of the Library's
  quotient Haar measure on `GL_n(F) \ GL_n(𝔸)` restricted to the slab
  `1 ≤ |det g| < e^n`.

**Why this is the quotient measure.** Cogdell integrates over
`Z_n(𝔸) GL_n(F) \ GL_n(𝔸)` and leaves its measure implicit. The natural choice is the
quotient `dg / d^×a` of the measure on `GL_n(F) \ GL_n(𝔸)` by the measure `d^×a` on
`F^× \ 𝔸^× = Z_n(F) \ Z_n(𝔸)`. The definition above realizes it without constructing a
quotient measure. The fiber of the projection over the class of `g` is
`{GL_n(F) a g : a ∈ 𝔸^×} ≅ F^× \ 𝔸^×`, because `Z_n(𝔸) ∩ g⁻¹ GL_n(F) g = Z_n(F)`. Since
`|det(a g)| = |a|^n |det g|`, the slab cuts this fiber in
`F^× \ {a : c ≤ |a| < e c}` with `c = |det g|^(-1/n)`. By translation by an idele of
norm `c`, this has volume `1` for `d^×a = ideleMeasure F`. So for every function `h` on
the quotient, `∫ h d(centralQuotientMeasure) = ∫ h d(dg / d^×a)`. With this measure, the
unfolding `I(s) = Ψ(s)` holds with constant `1`. The section `F(g, Φ; s, η)` uses the
same `d^×a`, and a rescaling of `d^×a` would multiply the section and divide the
quotient measure by the same constant. This is an explanation; the Lean definition does
not depend on it, and the module does not prove it.

## The integrals

* `equalIntegrand F χ φ φ' Φ s q` is `φ(g) φ'(g) E(g, Φ; s, η)` at the representative
  `g = q.out` of a class `q`. When `φ` and `φ'` are automorphic with central characters
  `ω` and `ω'` and `χ = ω ω'`, the product is left `Z_n(𝔸) GL_n(F)`-invariant (Cogdell
  p.209: under the center `E` transforms by `η⁻¹`), so the value does not depend on the
  representative.
* `equalIntegral F χ φ φ' Φ s` is Cogdell's

  `I(s; φ, φ', Φ) = ∫_(Z_n(𝔸) GL_n(F) \ GL_n(𝔸)) φ(g) φ'(g) E(g, Φ; s, η) dg`

  (p.209), for `dg = centralQuotientMeasure F n`. Cogdell sets `η = ω ω'`. Here `χ` is a
  separate argument; the statement modules take `χ = ω ω'`. The integral uses the
  series itself, not its continuation. So the definition is the integral of Cogdell's
  formula only where the series converges. Beyond that region, the theorem statements
  speak about continuations of `I`.
* `equalWhittakerIntegrand F W W' Φ s q` is `W(g) W'(g) Φ(e_n g) |det g|^s` at the
  representative `g = q.out` of a class `q ∈ N_n(𝔸) \ GL_n(𝔸)`.
* `equalWhittakerIntegral F W W' Φ s` is

  `Ψ(s; W, W', Φ) = ∫_(N_n(𝔸) \ GL_n(𝔸)) W(g) W'(g) Φ(e_n g) |det g|^s dg`

  (Cogdell p.210, the unfolded form of `I`), for the Library's
  `whittakerQuotientMeasure F n`. That measure is the image of the Haar quotient measure
  on `N_n(F) \ GL_n(𝔸)`, so `N_n(F) \ N_n(𝔸)` has volume one, which is the normalization of
  the Library's global Whittaker functions. `W` and `W'` are arbitrary functions; the
  unfolding statement takes `W = W_φ` for `ψ` and `W' = W'_φ'` for `ψ⁻¹`.

Lean `∫` is total: each integral is the Bochner integral, which is `0` when the
integrand is not integrable. No integrability is asserted here.

## The pole set

`equalPoleSet F n χ` is the set of `s` for which there is `w ∈ ℂ` with `χ(a) = |a|^w`
for all ideles `a` and `s = -w/n` or `s = 1 - w/n`. If `χ` is not of the form `|·|^w`,
the set is empty.

Cogdell (p.209) takes `η` unitary. If `η` is unramified of the form `η(a) = |a|^(inσ)`
with `σ ∈ ℝ`, the poles are at `s = -iσ` and `s = 1 - iσ`. Otherwise there are none.
This is the case `w = inσ`. Cogdell's "ramified" means not of the form `|·|^(inσ)`.
Here `χ` need not be unitary, so `w` is allowed to be any complex number. The reason is
the Poisson summation formula in Cogdell (p.209): the boundary terms are
`Φ(0) ∫_(|a| ≤ 1) |a|^(ns + w) d^×a` and `Φ̂(0) ∫_(|a| ≤ 1) |a|^(ns + w - n) d^×a`, which
have their poles at `ns + w = 0` and `ns + w - n = 0`. Because `|·|` maps `𝔸^×` onto
`ℝ_(>0)`, `w` is unique when it exists.

## Deviations from the source

* The character is a parameter `χ` of the definitions instead of being fixed as
  `ω ω'`. The statement modules make that choice.
* The characters need not be unitary. The pole set is extended accordingly (see above).
* The measures are fixed as explained above. Cogdell does not normalize them.
* Sums and integrals are Lean's total `tsum` and Bochner integral.
