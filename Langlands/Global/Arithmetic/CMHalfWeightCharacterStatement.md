# Conjugate-inverse Hecke characters of weight one

Worker 84. This contribution defines the proposition
`Langlands.Global.CMHalfWeightCharacterStatement.{u}` in
`Langlands/Global/Arithmetic/CMHalfWeightCharacterStatement.lean`. It is an
existence assertion and is not proved here.

## Statement

Let `K : Type u` be a CM number field and let `c` be its actual arithmetic
complex conjugation, `IsCMField.complexConj K`. Let `t : InfinityType K` be
an integral infinity type that is pure of weight one,
`t.IsPureOfWeight 1`: `t σ + t σ̄ = 1` for every complex embedding `σ`.
Let `S` be a finite set of finite places of `K` that is disjoint from its
image under the place map of `c` (the hypothesis used by the existing CM
statements in `CMCharacterStatement`). Then there is a Hecke character
`φ : HeckeCharacter K` with three properties.

1. `φ ∘ c = φ⁻¹` on the idele-class group, with
   `AdelicFunctoriality.ideleClassComplexConj` for `c`.
2. For every archimedean idele `x`,
   `φ_∞(x) · ∏_τ |x_τ| = t_∞(x)`, where `x_τ` is the complex coordinate
   `InfinityType.coordinate τ x` and `t_∞` is
   `InfinityType.toCharacter t`. So at the place of the embedding `σ` the
   component of `φ` is `z ↦ z^{t σ} z̄^{t σ̄} / |z| = (z/|z|)^{2 t σ − 1}`.
   This is the defining equation of `Harris.IsAlgebraicAfterTwist 1 φ`
   (the power `1` is omitted), with the witness type fixed to be `t`.
3. `φ` is unramified at every place of `S` (`HeckeCharacter.IsUnramifiedAt`:
   trivial on the local integral units).

Since `t` has odd weight, every archimedean component is
`(z/|z|)^b` with `b` odd. In particular `φ_∞` is not trivial on `ℝˣ`.

## Original sources

M. Harris and R. Taylor, *The Geometry and Cohomology of Some Simple
Shimura Varieties*, Annals of Mathematics Studies 151 (2001). Registered
source `harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`. Read
directly for this contribution: Proposition VII.2.7 (printed p.238, PDF
p.246) and Corollary VII.2.8 with its proof (printed pp.244–245, PDF
pp.252–253).

Proposition VII.2.7 uses a character `φ` of `𝔸_{L₁}ˣ/L₁ˣ` on a CM field
`L₁` with (1) `φ^c = φ⁻¹`, (2) `φ_∞ = 1` if `[L₂ : L₁]` is odd, (3) if
`[L₂ : L₁]` is even, `φ_x(z) = (τz/|τz|)^{±1}` at every archimedean place,
and (4) `φ_y` unramified at one finite place `y`. The proof of Corollary
VII.2.8 shows that such a `φ` exists when `y` is unramified over `L₁⁺`.
Through a diagram with rows ending in `Cl(L₁)` and `Cl(L₁)^{1+c}`, whose
lower row contains `L₁ˣ N_{L₁/L₁⁺}(𝔸_{L₁}ˣ)`, the proof reduces to defining a
character of `∏_x O_{L₁,x}ˣ / (O_{L₁,y}ˣ · N_{L₁/L₁⁺}(∏_x O_{L₁,x}ˣ))` equal to
`φ_∞⁻¹` on the global units. It then checks that the global units meeting
this subgroup are totally real units of norm one to `ℚ`, on which `φ_∞` is
trivial.

M. Harris, *The local Langlands conjecture for GL(n) over a p-adic field,
n < p*, Invent. Math. 134 (1998). Registered source
`harris-1998-local-langlands`, SHA-256
`7934239ea37d0b91f741ae70c2ac157fe5d619cda4dd992ac24e39ae460c375b`. Read
directly: printed p.195 (PDF p.19, and
lines 1180–1219 of the supplied TeX source `math_9611226v1.tex`). For
automorphic induction to `GL(n)`, Harris takes archimedean components
`(z/z̄)^{a(ν)/2}` with `a(ν) ≡ n − 1 (mod 2)`. On the same page his
construction extends a character trivial on `(E'_{0,𝔸})ˣ` and chooses
components trivial on `ℝˣ`. A component `(z/z̄)^{a/2} = (z/|z|)^a` with `a`
odd takes the value `−1` at `−1`. So the construction as written gives only
even `a(ν)`, and for even `n` the odd exponents need a separate character.
Harris–Taylor's `φ` in case (3) supplies it.
The Library's datum `Harris.IsProposition48Datum` requires
`IsAlgebraicAfterTwist ([E' : E] − 1) ξ`. When `[E' : E]` is even, a
character of the present kind on the base field `E`, pulled back by the
norm to `E'`, provides the odd exponents.

## Derived generalizations

The statement is a derived generalization of Harris–Taylor's `φ`. It is not
a verbatim numbered theorem.

- **Infinity type.** Harris–Taylor fix the exponents `±1`; that is
  `t σ ∈ {0, 1}`. Here `t` is any integral type of pure weight one, so the
  exponents are any odd integers `2 t σ − 1`. The proof of Corollary
  VII.2.8 uses that `φ_∞` is trivial on the totally real units of norm one
  to `ℚ`, and its diagram contains the archimedean norms
  `N_{L₁/L₁⁺}(L_{1,∞}ˣ)`, the positive reals at each place. For every type of
  pure weight one, `φ_∞` is `r^{t σ + t σ̄}/r = 1` on a positive real `r`, and
  `∏_v sign(α_v) = sign N_{L₁⁺/ℚ}(α)` on a totally real unit `α`. So both
  properties hold for every such `t`.
- **Places.** Harris–Taylor have one place `y` that is unramified over
  `L₁⁺`. Here there is a finite set `S` disjoint from its conjugate set.
  Each place of `S` is then split over `K⁺`. At such places every local unit
  of `K⁺` is a norm, which is the property the source argument uses at `y`.
  The disjointness hypothesis excludes inert places, which Harris–Taylor
  allow, and repeats the hypothesis of the published CM statements.

These remarks explain the provenance and the expected proof route. They are
not a proof, and the Lean file proves nothing.

## Boundaries

The statement prescribes neither finite components nor uniformizer values.
It has no regularity condition. It is independent of
`CMCharacterGlobalizationStatement`, whose characters all have anticyclotomic
integral types (even exponents of `z/|z|`).

It serves H2 of program `34b81620-20d7-4059-9b08-6bedd1c1c029`: the target
`HarrisDatumCharacterRealizationStatement` (module
`HenniartHarrisDatumStatement`) needs it when `[E' : E]` is even.
