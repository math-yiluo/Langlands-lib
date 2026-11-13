# Local values of distribution characters

The Jacquet–Langlands relation compares the characters of a
representation of `GL_n(F)` and of a representation of `D^×` at
corresponding regular elliptic elements. This module defines what it
means for a distribution character to have a value at a point. It
uses the Library's distribution character
`Langlands.Character.distribution μ ρ hρ` of an admissible
representation.

## Source

Deligne–Kazhdan–Vignéras (Bernstein–Deligne–Kazhdan–Vignéras 1984,
*Représentations des algèbres centrales simples p-adiques*,
introduction, printed p. 33, PDF page 37 of the registered readable
original) recall the definition. For an admissible representation `π`
and an element `φ` of the Hecke algebra of locally constant, compactly
supported measures, `π(φ)` has finite rank and the character of `π` is
the distribution `φ ↦ trace π(φ)`. Harish-Chandra showed that this
character is a locally constant function `χ_π` on the set `G_rg` of
regular elements. In other words, if `Supp(φ) ⊂ G_rg`, then
`trace π(φ) = ∫ χ_π(g) φ(g)`. Appendix A.3.c (printed p. 52, PDF
page 56) states the same formula with a Haar measure `dg`. Badulescu
2002 (`math0201117.tex`, §5, lines 2774–2778) likewise writes `χ_π`
for the character of a smooth representation of finite length, viewed
as a locally constant function on the regular semisimple set.

The Lean definitions below state the character identity of that
formula pointwise and locally. They do not assume Harish-Chandra's
theorem.

## Local values of a distribution

For a topological space `X` with a σ-algebra, a measure `μ` on `X`,
and a distribution `Θ : Distribution X` (a linear form on the
Schwartz–Bruhat space `SchwartzBruhat X` of locally constant, compactly
supported complex functions):

- `HasLocalValue μ Θ x c` holds when there is an open set `U`
  containing `x` such that `Θ f = c * ∫ f dμ` for every test function
  `f` whose support lies in `U`. Thus `Θ` agrees near `x` with the
  constant function `c` times `μ`.

- `exists_isCompact_isClopen_subset` proves that in a Hausdorff,
  locally compact, totally disconnected space every open neighbourhood
  `U` of `x` contains a compact open neighbourhood of `x`. The proof
  takes a compact neighbourhood inside `U` and then a clopen
  neighbourhood inside its interior, using Mathlib's
  `loc_compact_Haus_tot_disc_of_zero_dim`.

- `HasLocalValue.unique` proves that a local value is unique when `X`
  is Hausdorff, locally compact and totally disconnected with its Borel
  σ-algebra, and `μ` is finite on compact sets and positive on nonempty
  open sets. Given values `c` and `c'` on neighbourhoods `U` and `U'`,
  choose a compact open `K ∋ x` inside `U ∩ U'` and apply both
  identities to its indicator function
  `Hecke.TestFunction.characteristic`. Its integral is
  `μ(K)`, which is finite and nonzero because `K` is compact, open
  and nonempty, so `c * μ(K) = c' * μ(K)` gives `c = c'`.

## Character values of representations

Let `G` be a Hausdorff, locally compact, totally disconnected
topological group, and let `ρ : Representation ℂ G V` be admissible
(`IsAdmissible ρ`, the Library's smooth plus finite-dimensional fixed
vectors under each open subgroup), with admissibility proof `hρ`.

- `HasCharacterValue ρ hρ g c` holds when, for every Haar measure `μ`
  on `G` with the Borel σ-algebra, the distribution character
  `Character.distribution μ ρ hρ`, given by
  `f ↦ trace (∫ f(y) ρ(y) dμ(y))`, has the local value `c` at `g`
  relative to `μ`. With `φ = f dμ` this is the DKV formula
  `trace π(φ) = ∫ χ_π φ` with `χ_π` equal to the constant `c` near
  `g`. Where Harish-Chandra's function `χ_π` exists and is locally
  constant near `g`, `HasCharacterValue ρ hρ g c` holds exactly for
  `c = χ_π(g)`. Where no local value exists the predicate holds for no
  `c`.

  The predicate quantifies over all Haar measures in Mathlib's sense
  (`IsHaarMeasure`: left invariant, finite on compact sets and positive
  on nonempty open sets). No regularity or second countability is
  assumed, and in this generality two Haar measures need not be scalar
  multiples of each other as measures: Mathlib proves equality of
  measures up to a scalar only under inner regularity, regularity or
  second countability (`isMulLeftInvariant_eq_smul_of_innerRegular`,
  `isMulLeftInvariant_eq_smul_of_regular`, `isHaarMeasure_eq_smul`).
  What holds in general is the comparison of integrals: for two Haar
  measures `μ'` and `μ` there is a scalar `t = haarScalarFactor μ' μ`
  with `∫ f dμ' = t * ∫ f dμ` for every continuous compactly supported
  real function `f`
  (`integral_isMulLeftInvariant_eq_smul_of_hasCompactSupport`, applied
  to real and imaginary parts for complex functions). This comparison
  would suffice to show that one Haar measure gives the same predicate:
  the Schwartz–Bruhat test functions `f`, and the coordinate integrands
  `y ↦ f(y) ℓ(ρ(y) v)` defining the integrated action, are locally
  constant with compact support, so both the character and the
  integral `∫ f dμ` change by the same factor `t`. The Library has no
  scaling lemma for `Character.distribution`, so this is not proved
  here, and the definition requires every Haar measure. The Borel σ-algebra is installed locally
  with `letI : MeasurableSpace G := borel G`, as in the Library's
  other uses of Haar measures on groups without a global measurable
  structure.

- `HasCharacterValue.unique`: a character value is unique, by
  `HasLocalValue.unique` for Mathlib's Haar measure `Measure.haar`.

- `hasCharacterValue_iff_of_equivariant`: if `E : V ≃ₗ[ℂ] W`
  intertwines `ρ` and `σ`, then `ρ` and `σ` have the same character
  values. This uses the Library's
  `Character.distribution_eq_of_equivariant`.

- `exists_hasCharacterValue_mul_iff` gives the form in which the
  Jacquet–Langlands relation is used. Let `ρ` have value `a` at `g`
  and `σ` (a representation of a second such group `H`) have value
  `b` at `h`. Then a common `c` with `ρ` of value `s * c` at `g` and
  `σ` of value `c` at `h` exists if and only if `a = s * b`. The
  proof uses uniqueness.

## Finite-dimensional representations

- `isAdmissible_of_finiteDimensional`: a smooth representation on a
  finite-dimensional space is admissible, because every subspace of
  fixed vectors is finite-dimensional.

- `hasCharacterValue_trace`: a finite-dimensional admissible
  representation `ρ` has, at every `g₀ ∈ G`, the character value
  `trace ρ(g₀)`. This shows that `HasCharacterValue` is satisfiable,
  and it is the case used for `D^×` when `D` is a division algebra
  (irreducible smooth representations of the compact-modulo-centre
  group `D^×` are finite-dimensional). Fix a basis `b` of `V`. Each
  orbit map `g ↦ ρ(g) b_i` is locally constant (the Library's
  `Hecke.orbitMap_locallyConstant`), so
  `U = ⋂_i {g | ρ(g) b_i = ρ(g₀) b_i}` is an open neighbourhood of
  `g₀` on which `ρ(g) = ρ(g₀)`. For `f` supported in `U`, every
  coordinate functional of the integrated action
  `∫ f(y) ρ(y) dμ(y)` equals that of `(∫ f dμ) • ρ(g₀)`, by the
  Library's `Hecke.integratedAction_dual`, so the two operators agree.
  Taking traces, with `FiniteRankEnd.trace_eq_ambient` and
  `Character.finiteRankIntegratedAction_coe`, gives
  `Θ f = trace ρ(g₀) * ∫ f dμ`.

## What is not proved here

Harish-Chandra's theorem that the character of an irreducible
admissible representation of `GL_n(F)` has a value at every regular
semisimple element is not proved. DKV recall it as Harish-Chandra's
theorem. Badulescu 2002 (lines 2774–2778) uses the same fact for
smooth representations of finite length in any characteristic. The
Jacquet–Langlands relation built on this module includes, as part of
its condition, that the characters have values at corresponding
regular elliptic elements, so it does not assume that theorem.
