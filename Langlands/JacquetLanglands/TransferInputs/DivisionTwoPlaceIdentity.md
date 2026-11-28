# The two-place character identity from the global comparison

The module `Langlands.JacquetLanglands.TransferInputs.DivisionTwoPlaceIdentity`
states `DivisionTwoPlaceIdentityStatement`. In degree greater than one this
is the local output of Deligne–Kazhdan–Vignéras (DKV) §B.1.a–g for the units
of a division algebra. The identity relates products of characters at two
ramified places. Its distinguished term is `B ⊗ 1`, where `B` is the given
irreducible representation of `Dˣ` with unitary central character. In degree
one the identity follows by transport of representations of the two fields'
unit groups.

## Notation

- `F` is a nonarchimedean local field of characteristic zero and `D` a
  finite-dimensional central division algebra over `F` with its `F`-module
  topology, both in `Type u`, with `Module.finrank F D = n ^ 2`.
- `F₂` and `D₂` are a second such field and division algebra, in `Type`, with
  `Module.finrank F₂ D₂ = n ^ 2`. The statement provides them, with all their
  instances, existentially.
- `SmoothRep.{0, u, uW} ℂ Dˣ` is the category of smooth complex representations
  of `Dˣ` with carriers in `Type uW`. The same notation applies to `GL_n(F)` (carriers in
  `Type uV`) and for `GL_n(F₂)`, `D₂ˣ` (carriers in `Type`).
- `HasScalarCharacter ρ z ω` (`Langlands.Classification`) says that `ρ (z c)`
  acts by the scalar `ω c`; with `z = Units.map (algebraMap F D)` it says that
  the centre `Fˣ` of `Dˣ` acts through `ω`.
- `IsSquareIntegrable`, `IsAdmissible`, `Representation.IsIrreducible`,
  `Representation.Equiv`, `Corresponds` and `HasCharacterValue` come from
  `Langlands.JacquetLanglands.Relation` and its imports. They express
  square-integrability modulo the centre (with unitary central character),
  admissibility, irreducibility, equivalence of representations, the
  correspondence of a regular elliptic `g ∈ GL_n` and a regular `g'` of the
  division algebra with the same (reduced) characteristic polynomial, and
  local values of distribution characters.
- `Representation.trivial ℂ D₂ˣ ℂ` is the trivial representation on `ℂ`.

## The statement

`DivisionTwoPlaceIdentityStatement` says the following. Let `F`, `D`, `n` be as
above and let `B : SmoothRep.{0, u, uW} ℂ Dˣ` be irreducible and admissible, with
`HasScalarCharacter B.representation (Units.map (algebraMap F D)) ω` for some
`ω : Fˣ →* ℂˣ` with `‖ω z‖ = 1` for all `z`. The conclusion supplies the
following data.

1. `F₂`, `D₂` in `Type` as above.
2. `π₁ : SmoothRep.{0, u, uV} ℂ (GeneralLinear n F)` and
   `π₂ : SmoothRep.{0, 0, 0} ℂ (GeneralLinear n F₂)`, both irreducible and
   square-integrable modulo the centre (`h₁`, `h₂`).
3. a finite type `Q` and representations `τ q : SmoothRep.{0, u, uW} ℂ Dˣ`,
   admissible (`hτ`), irreducible and pairwise inequivalent.
4. for each `q`, a finite type `K q` and representations
   `σ q k : SmoothRep.{0, 0, 0} ℂ D₂ˣ`, admissible (`hσ`), irreducible and,
   for fixed `q`, pairwise inequivalent.
5. multiplicities `m q k : ℕ`, all positive.
6. indices `q₀ : Q` and `k₀ : K q₀` with `τ q₀` equivalent to `B` and
   `σ q₀ k₀` equivalent to the trivial representation of `D₂ˣ` on `ℂ`.

For all `x : GeneralLinear n F`, `x' : Dˣ`, `y : GeneralLinear n F₂`
and `y' : D₂ˣ` with `Corresponds F D x x'` and `Corresponds F₂ D₂ y y'`, this data gives
character values `a` of `π₁` at `x`, `b` of `π₂` at `y`, `c q` of `τ q` at `x'`
and `d q k` of `σ q k` at `y'` with

`a * b = ∑ q, c q * ∑ k, (m q k : ℂ) * d q k`.

The universes `u`, `uV`, `uW` are free.

## Why the statement is true

In degree `n = 1`, the algebra is its base field and
`GL₁(F) ≃ Fˣ ≃ Dˣ`. The central scalar action and irreducibility make `B`
one-dimensional. Realize its transported character on a one-dimensional
carrier in `Type uV` for `π₁`. Take any characteristic-zero nonarchimedean
local field `F₂ : Type` and set `D₂ = F₂`, with trivial representations on
both auxiliary groups. Each split central quotient is a point and the
central characters are unitary, so the split representations are
square-integrable modulo the centre. The matching polynomials have degree
one and identify the scalar on each side. Thus the singleton family with
`τ = B`, `σ = 1` and multiplicity one gives the identity.

For `n > 1` use DKV §B.1 with `m = 1` and a two-element ramified set `S`.

1. *Globalization.* Choose a number field `K` with finite places `v, w`,
   with `K_v ≅ F`. The Albert–Brauer–Hasse–Noether theorem gives a central
   division algebra `A` whose invariants at `v, w` are `inv_v(D)` and
   `-inv_v(D)` and vanish everywhere else. Both invariants have order `n`,
   so `A` and `D₂ = A ⊗ K_w` have degree `n`, and `A ⊗ K_v ≅ D`. Put
   `F₂ = K_w`. One can take `K` finite over `ℚ` in `Type`, so the auxiliary
   field and algebra are in `Type`.
2. *Central character.* Choose an unramified unitary character `χ` of
   `Fˣ` such that `ω χ^n` takes the value one on a uniformizer, using an
   `n`th root of its prescribed inverse value. The scalar action on
   `B ⊗ (χ ∘ Nrd)` is `ω χ^n` because `Nrd(z) = z^n` for a central
   scalar `z`. Smoothness gives open kernel on the compact unit group, so
   the new central character has finite order. Apply Grunwald–Wang to
   prescribe this character at `v` and the trivial character at `w` in
   one unitary adelic central character. DKV §B.1.g, citing Appendix 3
   and Henniart, globalizes the twisted `B` at `v` and the trivial
   representation at `w` to an automorphic representation `Π'` of
   `Aˣ(𝔸_K)`, supercuspidal at an auxiliary place `r ∉ S` where `A`
   splits.
3. *Comparison of trace formulas* (§B.1.a). In the fixed unitary adelic
   central character, take test functions `φ` on `GL_n(𝔸_K)` and `φ'`
   on `Aˣ(𝔸_K)` with equal components outside `S`, a supercuspidal
   component at `r`, and matching orbital integrals at `v, w` extended
   by zero off the matching set. Test functions supported near the
   corresponding regular pairs satisfy the regular elliptic support
   condition. The simple trace formulas give
   `trace R(φ) = trace R'(φ')`. The Library's
   `Langlands.TraceFormula.DivisionAlgebraSimpleTraceComparisonStatement`
   formulates a related comparison on the canonical split-centre
   quotient, using the discrete spectrum of the split group.
4. *Fixing the component outside `S`* (§B.1.b). After selecting the
   supercuspidal component at `r`, the separation argument fixes the
   full tensor factor `Π'^S`, including ramified split places and
   archimedean places as well as the unramified Hecke eigensystem. This
   leaves a comparison of traces on the product over `S`, with
   multiplicities of automorphic representations with that outside
   component. Strong multiplicity one and the supercuspidal component
   at `r` leave at most one cuspidal split term, of multiplicity one if
   it exists (§B.1.c).
5. *Finiteness on the division side* (§B.1.d–e and Appendix 2). Compare
   the `L`- and `ε`-factors of each completion of `Π'^S` on the division
   side with those of `Π'`. For each rational prime the weighted sum
   of the conductor exponents over the places of `S` above it is fixed.
   Lower bounds for the individual exponents give upper bounds, hence
   a common compact open level. The finiteness assertion of §B.1.e
   gives finitely many completions at this level. Group their local
   factors by the class at `v` and then by the class at `w`, adding
   the positive integral multiplicities. The distinguished completion
   `Π'` supplies the term `(B ⊗ (χ ∘ Nrd), 1)`.
6. *Passage to characters.* The finite trace identity becomes a
   character identity by taking matching test functions of small
   support about corresponding regular pairs. The finite-dimensional
   smooth division characters equal their dimensions on a common
   identity neighbourhood at each place. Density of regular elements
   gives a regular pair there, at which the division sum is strictly
   positive. Matching then gives a nonempty split term with a nonzero
   character on the elliptic product. Its two local factors are
   generic by Shalika's theorem. Each character is nonzero somewhere
   on the corresponding elliptic set, so §B.1.c applies Zelevinsky's
   classification to give the required square-integrable factors.
7. *Undoing the twist.* Twist the split factor at `v` by
   `χ⁻¹ ∘ det` and each division factor there by `χ⁻¹ ∘ Nrd`. Matching
   polynomials give `det x = Nrd x'`, so both sides are scaled by the
   same scalar at every corresponding pair. The twist preserves
   inequivalence, admissibility and square-integrability modulo the
   centre. The distinguished term now has first factor equivalent to
   `B`.

The product comparison is unsigned, as in §B.1.f. The two local signs
`(-1)^(n-1)` multiply to one.

The statement is also a consequence of the local Jacquet–Langlands
correspondence (with `π₁` the partner of `B`, `π₂` the Steinberg
representation of `GL_n(F₂)` and one term). Using that implication as an
input to a proof of the local correspondence would be circular.

## Derived content and differences from the sources

- DKV work with the product groups `G_S`, `G'_S` over the finite set `S` of
  ramified places and with sums over automorphic representations. In degree
  greater than one, the choice of opposite invariants gives `S = {v, w}`.
  This statement records the identity of character values after the
  finiteness step and groups the sum by the class of the component at
  the first place.
- The second field `F₂`, the division algebra `D₂` and all representations at
  the second place are existential. In degree greater than one they come
  from the globalization.
- The globalization prescribes a trivial component at the second place.
  DKV use the unit representation at the places of `S ∖ v` in §B.1.h
  and B.1.j.
- `π₁`, `π₂` are asserted square-integrable (with unitary central character),
  as DKV §B.1.c shows for the components of `Π`.
- `CharZero F` is DKV's hypothesis (local integrability of characters).

## Sources

- P. Deligne, D. Kazhdan, M.-F. Vignéras, *Représentations des algèbres
  centrales simples p-adiques*, in J. N. Bernstein, P. Deligne, D. Kazhdan,
  M.-F. Vignéras, *Représentations des groupes réductifs sur un corps local*,
  Hermann, 1984, pp. 33–117. Registered as
  `bdkv-1984-representations-local-field` (printed page = PDF page − 4):
  - §B.1.a–b, printed p. 78 and p. 79 (top): the comparison
    `trace π(φ) = trace π'(φ')` and the removal of the places outside `S`;
  - §B.1.c, printed p. 79: multiplicity one for `GL_n`, genericity and
    square-integrability of the components;
  - §B.1.d–e, printed pp. 79–81: finiteness through `L`- and `ε`-factors;
  - §B.1.f–g, printed pp. 81–82: the comparison formula on
    `G_S^ell ↔ G'^reg_S` with natural multiplicities, and globalization of
    every `π' ∈ E(G'_S, ω_S)`;
  - §B.1.h and B.1.j, printed p. 82: the unit representation at the other
    places of `S`;
  - Appendix 2, printed pp. 108–109, and Appendix 3, printed pp. 110–112,
    for finiteness at fixed level and globalization.
- E. Artin and J. Tate, *Class Field Theory*, AMS Chelsea edition (2009),
  Chapter X, §2, Theorem 5, printed p. 80 (PDF p. 89). Registered as
  `artin-tate-2009-class-field-theory`. This gives the finite-order
  Hecke character with the prescribed local components, allowing twice
  the least common multiple of their periods.
- A. I. Badulescu, *Correspondance de Jacquet–Langlands pour les corps locaux
  de caractéristique non nulle*, Ann. Sci. ÉNS 35 (2002). Registered as the
  folder `badulescu-2002-jl-char-p`. Propositions 5.4–5.7 and the proof
  of Proposition 5.8, §5, pp. 733–735 (TeX source `math0201117.tex`,
  lines 3045–3145) give a finite trace identity and its passage to a
  character identity on the product over the ramified set
  `V = {v₀, …, v_m}`. The auxiliary split factors there are Steinberg and
  the division sum ranges over irreducibles of the full product.
  Character independence on the auxiliary division groups then selects
  the coefficient of the trivial auxiliary tuple for the signed
  one-place identity (5.2).
