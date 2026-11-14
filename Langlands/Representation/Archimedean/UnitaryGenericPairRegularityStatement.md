# Archimedean pair `L`-factors of unitary generic modules on `Re(s) ≥ 1`

Author: Worker 3657.

This module states the Archimedean case of Getz–Hahn, Theorem 11.5.2, for
irreducible admissible generic unitarizable `(𝔤, K)`-modules of `GL_n(ℝ)` and
`GL_n(ℂ)`. It defines two predicates and eight propositions in the namespace
`Langlands.Archimedean`. They are statement targets, not proofs; the module
contains no theorem. It imports `Representation.Archimedean.RealGenericParameterReduction`
(for `realBlockExponent`, which also brings in `GKModule`),
`Representation.Unitary.Basic` and `LocalFactor.ArchimedeanPairFactor`. It
changes no published file and introduces no new factor.

The non-Archimedean case for p-adic fields is the published
`Langlands.RankinSelberg.UnitaryGenericLPolynomialNonvanishingStatement`.

## Sources

- Getz and Hahn, *An introduction to automorphic representations*, 2024
  (registered source `getz-hahn-2024-automorphic-representations`; PDF page =
  printed page + 11 in Chapter 11).
  - §11.5, printed page 304 (PDF page 315): `F` is a local field and `π`, `π'`
    are irreducible admissible generic representations of `GL_n(F)` and
    `GL_m(F)`.
  - Printed page 305 (PDF page 316): "In the Archimedean case, one actually
    defines `L(s, π × π')` using the Archimedean local Langlands
    correspondence … We will explain this in more detail in §12.3."
  - Theorem 11.5.2, printed page 305 (PDF page 316): "If `π` and `π'` are
    unitary, then `L(s, π × π')` is holomorphic and nonzero for `Re(s) ≥ 1`."
    For the Archimedean case GH refer to [BR94a, §2] (Barthel–Ramakrishnan
    1994). That paper is not in the project literature and is not used here.
- Knapp and Vogan, *Cohomological induction and unitary representations*,
  1995 (registered source `knapp-vogan-1995-cohomological-induction`; PDF
  page = printed page + 22 in the Introduction).
  - Display (0.5), printed page 6 (PDF page 28): a Hermitian form on a
    `(𝔤, K)`-module is invariant if `⟨π(X)v₁, v₂⟩ = −⟨v₁, π(X)v₂⟩` for
    `X ∈ 𝔤₀` and `⟨π(k)v₁, π(k)v₂⟩ = ⟨v₁, v₂⟩` for `k ∈ K`; the module is
    infinitesimally unitary if it admits a positive definite invariant
    Hermitian form.
  - Theorem 0.6(a), printed page 7 (PDF page 29): every irreducible
    admissible infinitesimally unitary `(𝔤, K)`-module is the underlying
    `(𝔤, K)`-module of an irreducible unitary representation on a Hilbert
    space.
- Badulescu and Renard, *Unitary dual of GL(n) at archimedean places and
  global Jacquet–Langlands correspondence*, Compositio Math. 146 (2010)
  (registered source `badulescu-renard-2010-unitary-dual`; journal PDF page =
  printed page − 1113).
  - Theorem 3.1 and Theorem 3.3, printed pages 1124–1125 (PDF pages 11–12):
    the Langlands classification of `GL(n, A)`, `A = ℝ, ℂ, ℍ`, by multisets of
    essentially square-integrable representations, with its uniqueness.
  - Definition 7.1, conditions U(0)–U(4) and Theorem 7.2 (Tadić's
    classification of the unitary dual), printed pages 1129–1131 (PDF pages
    16–18); Proposition 9.1 (`ν_δ = ν` for `A = ℂ`) and Proposition 9.4 (for
    `A = ℝ`), printed pages 1132–1133.
  - Section 8, printed page 1131 (PDF page 18), written for `GL(n, ℝ)`:
    Theorem 8.1 (Vogan, Kostant): for a quasi-split real reductive group, an
    irreducible representation is generic if and only if it is irreducibly
    induced from a generic limit of discrete series; the remark after it
    replaces "limit of discrete series" by "essentially tempered" and notes
    that for `GL(n, ℝ)` all essentially tempered representations are generic.
    Theorem 8.2: the generic irreducible unitary representations form the
    free commutative monoid, under `×`, on `u(δ, 1) = δ` and
    `π(δ, 1; α) = ν^α δ × ν^(−α) δ`, with `δ ∈ D^u` a unitary
    square-integrable representation of `GL(1, ℝ)` or `GL(2, ℝ)` and
    `0 < α < 1/2`; every product of basis elements is irreducible.
- Knapp 1994 (`knapp-1994-archimedean-llc`) through the published
  `StandardModule` Markdown, for the blocks and their Weil-group
  representations.

## Declarations

### `IsRealUnitarizableGKModule n ρ π` and `IsComplexUnitarizableGKModule n ρ π`

For a complex vector space `V`, a representation
`ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) V` of `O(n)` and a Lie
algebra map `π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V`, the
real predicate is

```lean
∃ b : Langlands.InvariantPositiveForm ρ, ∀ (X : Matrix (Fin n) (Fin n) ℝ) (v w : V),
  b.inner (π (1 ⊗ₜ X) v) w + b.inner v (π (1 ⊗ₜ X) w) = 0
```

`InvariantPositiveForm ρ` (module `Unitary.Basic`) is a positive definite
Hermitian form on `V` (Mathlib's `InnerProductSpace.Core ℂ V`, conjugate-linear
in the first argument) with `⟨ρ(k)v, ρ(k)w⟩ = ⟨v, w⟩` for every `k`. The
displayed clause says that every real matrix `X ∈ 𝔤₀ = 𝔤𝔩_n(ℝ)` acts by a
skew-Hermitian operator. Together these are exactly KV's (0.5): the predicate
is KV's "infinitesimally unitary". No topology or completion is involved.

The complex predicate is the same for `ρ` a representation of
`U(n) = Matrix.unitaryGroup (Fin n) ℂ` and `π` on
`ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ`, with `X` ranging over all complex matrices,
that is over `𝔤₀ = 𝔤𝔩_n(ℂ)` regarded as a real Lie algebra. This is the
convention of the published `IsComplexGKModule`.

### Exponent bounds

`RealUnitaryGenericExponentBoundStatement.{uV}`: for every `n`, every
`V : Type uV` with `AddCommGroup` and `Module ℂ` structures, every `ρ`, `π` as
above and every `ds : List RealBlock`, if

- `IsRealGKModule n ρ π`, `IsIrreducibleGKModule ρ π`, `IsAdmissibleGKModule ρ`,
  `IsRealGenericGKModule n π` (the published predicates of `GKModule`),
- `IsRealUnitarizableGKModule n ρ π`, and
- `HasRealStandardParameter n ρ π ds` (published, `GKModule`: an injective
  `(𝔤, K)`-intertwiner from the `O(n)`-finite functions of the Library's
  standard module of `ds` into `V`, with `ds` of total rank `n`),

then `|realBlockExponent x| < 1/2` for every block `x ∈ ds`.
`realBlockExponent` (published, `RealGenericParameterReduction`) is the real
part of the block's exponent `t`: of `sgn^ε |·|^t` for a character block and of
`D ⊗ |det|^t` for a block induced from `(z/|z|)^m |z|^(2t)`.

`ComplexUnitaryGenericExponentBoundStatement.{uV}` is the same over `ℂ`, with
`IsComplexGKModule`, `IsComplexGenericGKModule`, `IsComplexUnitarizableGKModule`,
`HasComplexStandardParameter` and `ds : List ComplexCharacterData`; the
conclusion is `|x.exponent.re| < 1/2` for every character
`x : z ↦ (z/|z|)^m |z|^(2t)` of `ds`.

### Right half-plane regularity of pair `L`-factors

`RealPairLFactorRightHalfPlaneRegularityStatement`: for all
`ds ds' : List RealBlock` and `s : ℂ`, if
`0 < s.re + realBlockExponent x + realBlockExponent y` for every `x ∈ ds` and
`y ∈ ds'`, then `(realPairLFactor ds ds').denominator s ≠ 0`.

`ComplexPairLFactorRightHalfPlaneRegularityStatement`: the same for
`ds ds' : List ComplexCharacterData` and `complexPairLFactor`, with
`x.exponent.re + y.exponent.re`.

`realPairLFactor ds ds'` and `complexPairLFactor ds ds'` (published,
`ArchimedeanPairFactor`) are the `L`-factors of the tensor product of the
Weil-group representations of `ds` and `ds'`. They are values of the
structure `ReciprocalEntire`: `L(s) = 1 / P(s)` with `P = denominator`
entire and not identically zero. So `P(s) ≠ 0` says that `L` has no pole at
`s`, and `L(s) = 1/P(s)` is then nonzero.

### Getz–Hahn, Theorem 11.5.2, Archimedean case

`RealUnitaryGenericPairRegularityStatement.{uV, uW}` (the entry point): for
all `n m : ℕ`, `V : Type uV`, `W : Type uW` with their `AddCommGroup` and
`Module ℂ` structures, `(ρ, π)` on `V` for `GL_n(ℝ)`, `(ρ', π')` on `W` for
`GL_m(ℝ)`, and `ds ds' : List RealBlock`, if each of the two modules satisfies
the six hypotheses of the exponent bound (with `ds`, resp. `ds'`), then

```lean
∀ s : ℂ, 1 ≤ s.re → (realPairLFactor ds ds').denominator s ≠ 0
```

`ComplexUnitaryGenericPairRegularityStatement.{uV, uW}` is the same over `ℂ`
with `complexPairLFactor`.

### Reductions

`RealUnitaryGenericPairRegularityReductionStatement.{uV, uW}` is the
implication

```lean
RealUnitaryGenericExponentBoundStatement.{uV} →
  RealUnitaryGenericExponentBoundStatement.{uW} →
    RealPairLFactorRightHalfPlaneRegularityStatement →
      RealUnitaryGenericPairRegularityStatement.{uV, uW}
```

and `ComplexUnitaryGenericPairRegularityReductionStatement.{uV, uW}` is the
complex analogue.

## Correspondence with Getz–Hahn

- GH's `π`, `π'` are representations on topological spaces; here they are
  replaced by their underlying `(𝔤, K)`-modules, as in the published
  `RealGenericStandardParameterStatement`. Unitarity is replaced by KV's
  infinitesimal unitarity. The underlying `(𝔤, K)`-module of an irreducible
  unitary representation is infinitesimally unitary (KV (0.5)); conversely
  KV Theorem 0.6(a) shows that an irreducible admissible infinitesimally
  unitary module comes from an irreducible unitary representation. So the
  hypotheses describe the same objects.
- GH's `L(s, π × π')` is defined through the Archimedean local Langlands
  correspondence. Here it is the Library's pair factor of the standard
  parameters `ds` and `ds'`. For generic `π` the standard module is
  irreducible and `HasRealStandardParameter n ρ π ds` holds exactly when the
  sum of the Weil-group representations of the blocks of `ds` is the
  Langlands parameter of `π` (the published `StandardModule` Markdown,
  "Scope of the parameter predicates", from Knapp 1994, Theorems 1–2 and
  4–5). The pair factor is then the `L`-function of the tensor product of
  the two Langlands parameters. This identification is the Library's
  convention and is not restated in Lean.
- The parameters `ds`, `ds'` are hypotheses, not conclusions: existence of a
  standard parameter is the published `RealGenericStandardParameterStatement`
  (resp. `ComplexGenericStandardParameterStatement`), which this module does
  not assume. If a module had no standard parameter the propositions would
  hold vacuously for it.
- GH's "holomorphic and nonzero" is "the denominator does not vanish": see
  the previous section. Nothing is asserted about `Re(s) < 1`.
- Genericity: GH's standing hypothesis of §11.5. The Lean hypotheses
  `IsRealGenericGKModule` and `IsComplexGenericGKModule` are the published
  algebraic Whittaker-functional predicates. The intended truth argument below
  does not use them, so the comparison of algebraic and continuous Whittaker
  functionals is not needed.

## Why the statements are true

This is the intended argument, not proved in this module.

1. **Regularity.** The block factors are shifted `Γ_ℝ` and `Γ_ℂ` factors.
   By the published `realLFactor_regular_iff` and `complexLFactor_regular_iff`
   (module `ArchimedeanPresentation`), `P(s) = 0` exactly when for some block
   `s + t + ε = −2k` (character block of parity `ε`) or `s + t + |m|/2 = −k`
   (induced block, resp. complex character, of weight `m`), with `k ∈ ℕ`. The
   blocks of the pair presentation have exponents `t + t'`:
   `RealCharacterData.mul`, `ComplexCharacterData.mul` and
   `ComplexCharacterData.twistReal` add exponents, and
   `ComplexCharacterData.conj` keeps the exponent. A pole would therefore force
   `Re(s) + Re(t) + Re(t') ≤ 0`.
2. **Exponent bound, real case.** Let `A` be the injective intertwiner of
   `HasRealStandardParameter`. Its image is a nonzero subspace stable under
   `ρ` and `π`, so it is `V` by irreducibility: `V` is isomorphic to the
   `O(n)`-finite standard module of `ds`, which is therefore irreducible. By
   KV Theorem 0.6(a), `V` is the Harish-Chandra module of an irreducible
   unitary representation. It is irreducibly induced from an essentially
   tempered representation (the blocks are essentially square-integrable, or
   for weight-`0` induction blocks principal series of unitary characters
   twisted by `|det|^t`), so it is generic in the sense of BR by BR
   Theorem 8.1 and the remark after it. By BR Theorem 8.2 it is then an irreducible product of
   representations `δ` and `ν^α δ × ν^(−α) δ` with `0 < α < 1/2`, whose
   blocks have exponents of real part in `{0, α, −α}`; here `ν = |det|` and
   `ν_δ = ν` by BR Proposition 9.4, and `D ⊗ |det|^t` has Library exponent `t`.
   Standard modules of the same blocks in different orders have the same
   composition factors (`StandardModule` Markdown, derived choice 4), so by
   uniqueness in the Langlands classification (BR Theorem 3.3, Knapp 1994,
   Theorem 1) the blocks of `ds` agree, up to order, with these, a weight-`0`
   induction block being read as the sum of its two characters.
3. **Exponent bound, complex case (derived).** BR state Section 8 for
   `GL(n, ℝ)`. For `GL(n, ℂ)` the same deduction uses Tadić's classification
   (BR Theorem 7.2 for `A = ℂ`, with `ν_δ = ν = |·|_ℂ = |·|²` by BR
   Proposition 9.1) and the genericity criterion for quasi-split groups; the
   generic unitary representations are irreducible products of unitary
   characters and of `ν^α χ × ν^(−α) χ`, `0 < α < 1/2`. In the Library's
   normalization `(z/|z|)^m |z|^(2t) = (z/|z|)^m |z|_ℂ^t`, so `ν^α χ` has
   exponent of real part `α`. This adaptation is not stated in BR; it is
   recorded here as derived.
4. **Main statement.** With `Re(s) ≥ 1` and `|Re t|, |Re t'| < 1/2`,
   `Re(s) + Re(t) + Re(t') > 0`, so step 1 applies. This is the reduction
   statement.

## Relation to published statements

- `UnitaryGenericLPolynomialNonvanishingStatement` (module
  `RankinSelberg.UnitaryGenericLPolynomialNonvanishingStatement`) is the
  p-adic case of the same theorem; together with the real and complex
  statements here GH Theorem 11.5.2 is covered for p-adic, real and complex
  fields.
- `RealGenericStandardParameterStatement`,
  `ComplexGenericStandardParameterStatement` (module `GKModule`) and
  `RealLanglandsQuotientStatement` (module `RealGenericParameterReduction`)
  provide the standard parameters assumed here.
- Global use: Getz–Hahn's strong multiplicity one argument for `GL_n` needs
  regularity of `L(s, π_v × π'_v)` at Archimedean places for local components
  of unitary cuspidal representations (Task 6388). Passing from a cuspidal
  automorphic representation to the hypotheses here (its Archimedean
  components are irreducible admissible generic unitarizable `(𝔤, K)`-modules
  with a standard parameter) is not part of this module.

## Intended proof children

1. The two right half-plane regularity statements: elementary, from
   `realLFactor_regular_iff`, `complexLFactor_regular_iff` and the exponent
   arithmetic of the block products.
2. The two exponent bounds: deep, through KV Theorem 0.6, BR Theorems 8.1,
   8.2, 3.3 and Tadić's classification as above.
3. The two reductions: immediate from the definitions.

## Lean checks

The module compiles with `lean_check` in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (diagnostic `1e991f28`) with no errors
or warnings. Every proposition is a `def` returning `Prop`; the two predicates
are `def`s returning `Prop`. Inspection of the entry point
`RealUnitaryGenericPairRegularityStatement` (diagnostic `5cf87aba`) reports a
definition returning `Prop` with universe parameters `uV uW`, using only
`propext`, `Classical.choice` and `Quot.sound`. There is no `sorry` and no new
axiom.
