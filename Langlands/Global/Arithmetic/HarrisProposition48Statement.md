# Harris's Proposition 4.8

This module states Harris (1998), Proposition 4.8, over the Library's actual
arithmetic and automorphic objects. Under the hypotheses of Section 4, there
is a cuspidal automorphic representation `Π ∈ U(n,E)` that is a weak
automorphic induction of a given Hecke character `ξ`, and whose local
component at an auxiliary place is supercuspidal. The statement is a `Prop`
definition. Nothing here proves it.

## The statement

`Langlands.Global.Harris.Proposition48Statement` quantifies over the
following data:

- a prime `p`, a `p`-adic field `F : PadicField p` and an extension
  `F' : Extension F`;
- number fields `E`, `E'`, `L` with algebra maps `E → E' → L` and `E → L`;
- CM structures on `E` and `E'`;
- the instance `[CompactSpace (AdeleQuotient E)]` required by the published
  cuspidal classes, which the published `compactSpace_adeleQuotient` proves;
- a local reciprocity family `e` for `F`, characters `χ`, `χs` of `F'^×`, a
  subfield `K₀ ⊆ E`, place data `P`, `Ps`, and a Hecke character `ξ` of `E'`.

If `NormalizedReciprocity F e` and `IsProposition48Datum e χ χs K₀ P Ps ξ`
hold, it asserts that some rank
`r + 1` and some irreducible cuspidal class
`c : CuspidalOperatorRealization.IsoClass E r` satisfy all of:

1. `c.IsWeakAutomorphicInductionOf ξ`: some actual spectral presentation of
   `c` matches the Euler factors of `ξ` at almost all places, with Tate's sum
   over all places above (published `WeakAutomorphicInduction`). The
   published `IsWeakAutomorphicInductionOf.rank_eq` then gives
   `r + 1 = [E' : E]`, Harris's `n`.
2. `c.IsRegularAlgebraic`: the infinitesimal character of `c` is that of an
   irreducible algebraic representation (`Langlands/Automorphic/RegularAlgebraic`).
   This is Clozel's regular algebraic type, so `c ∈ Reg(n,E)`.
3. `c.IsConjugateSelfDual`: `Π ≅ Π̌ ∘ c` for the CM involution
   (published `ConjugateContragredient`, Harris's Theorem 1.2(ii)).
4. `c.HasSupercuspidalComponent Ps.v`: the local component at
   `v(*)₁ = Ps.v` is supercuspidal (`Langlands/Automorphic/SupercuspidalComponent`).

The universes are those of `F` (`uF`), `E`, `E'` and `L` (`uE`, `uE'`, `uL`),
and `uV` for the carriers of the local factors of the presentations
witnessing conditions 1 and 4.

## Hypotheses

`NormalizedReciprocity F e` is the published hypothesis
(`Langlands/LocalFactor/CommonClosure`) that the candidate family `e` of
local reciprocity maps is the normalized coherent one. The datum reads the
general-position condition on `χs` through `e`, by pulling `χs` back to a
character of `W_{F'}`. For an unnormalized `e` that condition concerns the
wrong Weil character, as the published `HarrisSetup` Markdown notes. That
Markdown also says this statement would assume the normalization. The
published Lemma 4.7 statements in
`Langlands/Global/Arithmetic/GeneralPositionStatement` assume it in the same
way.

`IsProposition48Datum` is the published definition in
`Langlands/Global/Arithmetic/HarrisSetup`. It packages Harris's Section 4
setup (pages 200–201) and the hypotheses of Proposition 4.8:

- `K₀` is imaginary quadratic and `p` splits in it;
- `L` is the normal closure of `E'/E`;
- `P` and `Ps` give the places `v₁` and `v(*)₁` above `p`, with completions
  matched to `F ⊆ F' ⊆ F̃`, and each of `v₁, c(v₁), v(*)₁, c(v(*)₁)` has a
  unique place of `L` above it;
- the two pairs of places differ;
- `χs` is in general position relative to `F`;
- `ξ` is algebraic in Harris's normalization for automorphic induction
  to `GL(n)`, `n = [E' : E]` (p.195): `IsAlgebraicAfterTwist (n - 1) ξ`,
  so `ξ · ‖·‖^{(n-1)/2}` has an integral infinity type. Moreover `ξ` is
  `E'/E`-regular and satisfies `ξ = ξ⁻¹ ∘ c`, with components `χ` at
  `v₁'` and `χs` at `v(*)₁'`.

Harris's Proposition 4.8 just says "algebraic". It introduces the
proposition as an extension of Proposition 2.4, and page 195 fixes the
parity of the infinity type for automorphic induction to `GL(n)`: each
archimedean component is `(z/z̄)^{b/2}` with `b ≡ n − 1 (mod 2)`. The
`HarrisSetup` Markdown (derived choice 11) shows that
`IsAlgebraicAfterTwist (n - 1) ξ` together with `ξ = ξ⁻¹ ∘ c` says exactly
this. The datum needs no separate degree parameter, since `n` is
`Module.finrank E E'`.

No hypothesis `n < p` appears. Harris's Section 4 treats the general case,
and the title's restriction is not a restriction on this proposition.

## Agreement with `U(n,E)`

Harris (p.185, repeated on p.186) defines `U(n,E) ⊂ C(n,E)` as the
`π ∈ Reg(n,E)` that satisfy the conditions of Theorem 1.2, for `E` as in
(ii). For a cuspidal `π` these conditions are:

- (i) there is a finite place `v(i)` with `π_{v(i)}` square-integrable and
  `v(i)` above a prime that splits in `K₀`;
- (ii) `E = E₀ · K₀` with `E₀` totally real, and `π ≅ π̌ ∘ c`.

Condition 2 above is `π ∈ Reg(n,E)`. For (ii), the published `HarrisSetup`
Markdown explains that `E` being CM with `K₀ ⊆ E` imaginary quadratic is
equivalent to `E = E₀ · K₀`; condition 3 is the isomorphism. For (i), take
`v(i) = Ps.v`. Condition 4 makes `Π_{Ps.v}` supercuspidal, and supercuspidal
representations are square-integrable modulo the center. The datum puts
`Ps.v` above `p` and makes `p` split in `K₀`. The statement therefore records
membership in `U(n,E)` through these conditions. It does not define
square-integrability separately. Membership in `C(n,E)` (existence of a
weakly associated compatible system) is Theorem 1.2. It belongs to the
cohomological branch and is not part of this statement.

The regular algebraic type is not restricted further: the Remark in Harris's
proof (p.202) stresses that the infinite component is "a priori an arbitrary
representation of cohomological type".

## Consistency of the infinity type

Conditions 1 and 2 constrain the same archimedean data, so the parity of
the datum must match the conclusion. By Harris's (2.4.1) (p.193), the
weak automorphic induction of `ξ` has, at a place `τ` of `E`, the
exponents of the components `ξ_w` for the places `w | τ` of `E'`. Under
the datum these are `(z/z̄)^{b_w/2}` with `b_w ≡ n − 1 (mod 2)`, so the
holomorphic exponents `±b_w/2` lie in `(n − 1)/2 + ℤ`. That is what
Clozel's `Alg(n)` requires, and relative regularity makes them distinct.
In the convention of `Langlands/Automorphic/RegularAlgebraic`, the
infinitesimal character is `λ = μ + δ` with `μ` dominant integral and
`δ = ((n−1)/2, …, −(n−1)/2)`. So `μ = λ − δ` is integral.

Even-rank check (`n = 2`, worked out in derived choice 11 of the
`HarrisSetup` Markdown): components `(z/|z|)^{±1}` at the two places above
`τ` satisfy the datum, and give `λ = (1/2, −1/2)` and `μ = (0, 0)`. The
rejected version of this statement (below) used integral `IsAlgebraic ξ`.
Then every `b_w` is even and `λ` is integral, so `μ = λ − δ` has
half-integral entries and condition 2 could not hold together with
condition 1 for that `ξ`. These remarks are not formalized.

## Not claimed

- The statement is not proved. Its proof needs Harris's Theorems 1.2 and 1.7,
  Arthur–Clozel base change and automorphic induction (Lemma III.6.4), and
  the descent argument of Lemma 1.6. These are separate obligations.
- The predicates in conditions 1 and 4 ask for some presentation. The Library
  does not prove that all presentations of a cuspidal class have isomorphic
  local components.
- Harris's proof (p.202) runs an induction over intermediate fields `E_i`,
  through Mackey constituents of ranks `n(a,i)`, for example `n(a,0) = 1`.
  Their parity can differ from that of `n`, so the parity normalization
  changes along the induction. A formal proof must track the half-integral
  twists by `‖·‖^{1/2}` that Harris's p.191 remark allows ("up to twisting
  by a half-integer power of the absolute value character"). The statement
  makes no claim about these intermediate steps.

## Source

- M. Harris, *The local Langlands conjecture for GL(n) over a p-adic field,
  n < p*, Invent. Math. 134 (1998), 177–210. Source
  `harris-1998-local-langlands` (PDF page = printed page − 176). Read:
  Reg(n,E), Theorem 1.2 and `U(n,E)` (pp.185–186); the remark on
  half-integer twists (p.191, TeX lines 866–875); Proposition 2.4 and
  (2.4.1) (p.193, TeX lines 1031–1049); the infinity type and its parity
  (p.195, PDF page 19, TeX lines 1186–1219); Section 4 setup (pp.200–201);
  Proposition 4.8 (p.201, TeX lines 1554–1561) and its proof with the
  Remark (pp.201–203, the induction at TeX lines 1583–1612).
- L. Clozel (1990), Définitions 1.8 and 3.12, through
  `Langlands/Automorphic/RegularAlgebraic`.

## Revision

This statement replaces candidate `66d7ff71-1c22-4ccb-bf8b-7a43be9a62e2`,
which Reviewer 3482 rejected because the datum then required `IsAlgebraic ξ`
(integral infinity type), contrary to the parity normalization of p.195 for
even `n`. The Lean statement is unchanged apart from its docstring. The
correction is in the datum: `Langlands/Global/Arithmetic/HarrisSetup` now
uses `IsAlgebraicAfterTwist ([E' : E] - 1) ξ` (its section Correction).
This version updates the Hypotheses section, adds the section on the
consistency of the infinity type and one item under Not claimed, and
cites pp.191–195 of Harris.
