# Uniform automorphy of intertwining integrals from two analytic parts

Module `Langlands.Global.AdelicIntertwiningAutomorphyReductionStatement` contains one
`Prop`-valued definition and no theorem.

## The statement

`Langlands.Global.IntertwiningUniformAutomorphyReductionStatement.{u}` is the implication

`IntertwiningSmoothSlicesStatement.{u} → IntertwiningUniformCenterIdealStatement.{u} →
IntertwiningUniformAutomorphyStatement.{u}`

between three propositions of the module `Langlands.Global.AdelicIntertwiningAutomorphyStatement`
(see its page for the common data and notation). Write `T λ` for the Library's intertwining
operator `hK.intertwiningOperator hK' iU l iV c π' w φ λ`, the value `M(w, λ)φ`.

- `IntertwiningSmoothSlicesStatement`: there is a threshold `R₀` such that for every
  `R₀`-regular `λ` every infinite slice of `T λ` is plot-smooth.
- `IntertwiningUniformCenterIdealStatement`: there are `R₀` and an ideal `J` of finite
  codimension in the center `𝔷` of the complex enveloping algebra such that for every
  `R₀`-regular `λ` every element of `J` annihilates every plot-smooth infinite slice of `T λ`.
- `IntertwiningUniformAutomorphyStatement`: there are `R₀` and such an ideal `J` such that for
  every `R₀`-regular `λ` the function `T λ` is automorphic on `V(𝔸)M'(F) \ G(𝔸)`
  (`IsAutomorphicFunctionOn` for `parabolicQuotientSubgroup F q iV l'`, the infinite part of
  `K` and `rho`) and `J` annihilates every plot-smooth infinite slice of `T λ`.

So the statement says that the remaining conditions in `IsAutomorphicFunctionOn` (left
invariance under `V(𝔸)M'(F)`, continuity, a finite level, finiteness under the infinite part of
`K`, and moderate growth) hold for all sufficiently regular `λ` without further hypotheses. The
statement does not assert either premise, and this module proves none of the three propositions.

The module `Langlands.Global.AdelicIntertwiningAutomorphyReduction` proves the statement
(`intertwiningUniformAutomorphyReduction`).

## Sources and provenance

The statement is derived. It isolates the two analytic parts of the conclusion that need
differentiation under the integral sign, and asserts that the other parts follow.

- C. Mœglin and J.-L. Waldspurger, *Spectral decomposition and Eisenstein series*, Cambridge
  University Press, 1995, registered as `moeglin-waldspurger-1995-spectral-decomposition`,
  chapter file `06.1_pp_78_100_Definitions.pdf` (SHA-256
  `948dbfd356c2f068c1dc793a52e4c700334eb5236b740f1c775da535b747111c`), II.1.6, Proposition (i),
  printed pp. 87–88 (PDF pp. 10–11): for `Re π` in the stated cone the intertwining integral
  "converges absolutely and uniformly when g varies in a compact set" and "defines an element
  of `A(U'(𝔸)M'(k)\G)_{wπ}`". The proof (p. 88) bounds the integral by an integral over the
  compact quotient `U'(k)\U'(𝔸)` of the absolutely convergent Eisenstein series of II.1.5.
- J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer.
  Math. Soc. 37 (2024), 187–234, registered as
  `bernstein-lapid-2024-meromorphic-continuation-eisenstein`, journal PDF
  `Bernstein-Lapid--On the meromorphic continuation of Eisenstein series--2024.pdf` (SHA-256
  `6acbe78adf3a7ddff4be0caa92b169f0e609d1245f674a71fbc6989d6aef9268`), §8.2, Lemma and its
  proof, p. 222 (TeX `1911.02342.tex` lines 3274–3290): "there exists a finite-codimensional
  ideal of `𝔷` (independent of `λ`) that annihilates `M(w, λ)φ`".

The split of the conclusion of `IntertwiningUniformAutomorphyStatement` into the two premises
and the remaining conditions is internal to the Library. It follows the route described in the
page of `Langlands.Global.AdelicIntertwiningAutomorphyStatement` ("What is not stated here"),
with moderate growth moved from the premises to the conclusion.
