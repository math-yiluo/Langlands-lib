# The Artin–Schreier line `Lψ(c/t)` has slope one

Laumon (1987), Exemple (2.1.2.8), p. 154: fix a uniformizer `π` of a henselian trait and let
`R' = R[π']/(π'^p + π π'^(p−1) − π)`, so that `1/π'` solves the Artin–Schreier equation
`(1/π')^p − (1/π') = 1/π`. Then `R'` is a henselian discrete valuation ring with residue field
`k` and uniformizer `π'`, and `η' → η` is a finite étale Galois covering with group `𝔽_p`, where
`a ∈ 𝔽_p` acts by `π' ↦ π'/(1 + aπ')`. The character `ψ⁻¹ : 𝔽_p → ℚ̄_ℓ^×` of this Galois group
defines a `G`-module of rank one and Swan conductor one, written `Lψ(1/π)` (Serre, *Local Fields*,
IV §2, Exercise 5, p. 72: for `y` of valuation `−n` with `p ∤ n`, `X^p − X = y` defines a cyclic
extension of degree `p` with `G_n = G` and `G_{n+1} = 1`).

This module carries out the row `ArtinSchreierBreak` of §4.1 of the [design note for Laumon's local Fourier bijection](../../../notes/henniart/laumon-local-fourier-weil-conjectures-design.md), with its statement
under the name of the row; the definitions `artinSchreierRoot`, `artinSchreierTranslation` and
`artinSchreierValue` are added to describe the character.

## Definitions

Let `k₀` and `k` be fields with `Algebra k₀ k`; in the statement both are finite, `k₀` with
`q` elements is the field of the additive character `ψ : k₀ → E`, `E = PadicAlgCl ℓ`, and `k` is
the residue field of the trait `X = LaurentSeries k`, the completion `k((t))` of the end traits of
`Langlands.Correspondence.Laumon.Traits`. Write `Ω = SeparableClosure X` and `c/t` for the
Laurent series `HahnSeries.single (-1) c`.

- `artinSchreierRoot k₀ k c` is a root `u ∈ Ω` of the Artin–Schreier–Lang equation
  `u^q − u = c/t`, `q = Nat.card k₀`, chosen by `Classical.epsilon`. A root exists, since
  `T^q − T − c/t` is separable and `Ω` is separably closed.
- `artinSchreierTranslation k₀ k c σ`, for `σ ∈ Gal(Ω/X)`, is an element `a_σ ∈ k₀` with
  `σ u = u + a_σ`, chosen by `Classical.epsilon`. Since `σ u` is again a root, `σ u − u` is a root
  of `T^q − T`, whose roots are the `q` elements of `k₀`; so `a_σ` exists and is unique, and it
  does not depend on the root `u`.
- `artinSchreierValue k₀ k ψ c σ = ψ(−a_σ)`. With `w = 1/π'`, Laumon's `a ∈ 𝔽_p` acts by
  `w ↦ w + a` and the character is `ψ⁻¹(a) = ψ(−a)`; this is the same convention.

Laumon's example is the case of the prime field `k₀ = 𝔽_p` (his character `ψ : 𝔽_p → ℚ̄_ℓ^×`
of (0.2), p. 134) and `c = 1`, with `π = t`; the residue field `k` may be any finite field
containing `𝔽_p`. For a general `k₀` with `q` elements, the Lang isogeny of the additive group
over `k₀` (Laumon (1.1.3), pp. 138–139) has kernel `k₀` and is, up to sign, `u ↦ u^q − u`; it
takes the place of the Artin–Schreier isogeny, whose kernel is `𝔽_p`, and `ψ` is a character
of `k₀`. For `c ≠ 0` the polynomial `T^q − T − c/t` is irreducible over `X` (see the pole
computation below), so the splitting field `X(u)` has degree `q` and Galois group `k₀`, acting by
translations. For `c = 0` the polynomial splits over `X`, since its roots are the elements of
`k₀ ⊆ k`; then every `a_σ` is `0` and the character is trivial.

The pole `c/t` of order one is the restriction of the Fourier kernels `Lψ(t'/t)`, `Lψ(x x')` at
the points where the other variable is `c` (Laumon (2.4.2.1)–(2.4.2.3), pp. 162–163). A finite
field `k ⊇ k₀` is the residue field of the finite constant extension `k((t))` of `k₀((t))`; the
kernel over `k₀` pulled back to it and specialized at a point `c ∈ k` is the equation
`u^q − u = c/t` with `q = |k₀|`, whose Galois group for `c ≠ 0` is still the group of
translations by `k₀`.

## `ArtinSchreierPoleOneStatement`

For finite fields `k₀ ⊆ k` (any `Algebra k₀ k`), every prime `ℓ` and every nontrivial additive
character `ψ : k₀ → E`, with `X = LaurentSeries k` made a local field by the Library's
`Langlands.LocalField.Laurent.valuativeRel k`:

1. for every `c ∈ k`, the values `artinSchreierValue k₀ k ψ c σ` are those of a homomorphism
   `χ_c : Gal(Ω/X) →* Eˣ` whose line `ladicCharacterLine χ_c` is continuous and has a finite
   model: `Lψ(c/t)` is a `G`-module in Laumon's sense;
2. for `c ≠ 0` and every homomorphism `χ` with these values, the line has the single slope `1`
   (`slopeSupport = {1}` with `f` the identity) and `s = 1`;
3. for `c ≠ c'` and homomorphisms `χ`, `χ'` with the values for `c` and `c'`, the line of
   `χ χ'⁻¹`, the ratio `Lψ(c/t) ⊗ Lψ(c'/t)⁻¹` of the two Artin–Schreier kernels with linear
   parameters `c` and `c'`, has the single slope `1` and `s = 1`.

The values determine the homomorphism, so in clauses 2 and 3 the hypothesis only names the
character of clause 1. The statement is the Galois-theoretic one of Laumon's example: the
module `Lψ(1/π)` is defined there from the Galois group of the Artin–Schreier covering, as
here. It does not compare this character with the monodromy of an Artin–Schreier sheaf.
The hypothesis `ℓ ≠ p` is not needed: the character has finite image.

### Pole computation

The proof route is the following. For every `c ∈ k` with `c ≠ 0`, `T^q − T − c/t` is
irreducible over `k((t))` (weil-conjectures `LaurentSeries.irreducible_X_pow_sub_X_sub_C_single`,
for a pole coefficient in `k`). Its roots in `Ω` are the `u + a`, `a ∈ k₀`, since `a^q = a`; they
all lie in `M = X(u)`, so `M` is the splitting field, Galois of degree `q` over `X`. As `u` and
`u + a` have the same minimal polynomial and `Ω` is a normal extension of `X`, some
`σ ∈ Gal(Ω/X)` maps `u` to `u + a` (Mathlib's `Normal.minpoly_eq_iff_mem_orbit`); so `Gal(M/X)`
is `k₀`, acting by translations. The same argument over an algebraic closure of `X` is
weil-conjectures `LaurentSeries.exists_algEquiv_apply_eq_add_C_of_pow_sub_eq_single_of_ne_zero`
(pole coefficient in `k`); the version over the separable closure follows, as above, from the
normality of `Ω`, or by restriction, since every automorphism of an algebraic closure maps the
separable closure inside it onto itself. In the normalized
valuation of `M`, `v(u) < 0` and `q v(u) = −v(t) = −e`; with `e ≤ q` this gives `e = q`,
residue degree one and uniformizer `π = u⁻¹`. For the translation by `a ≠ 0`,
`σ_a(π) − π = −a/(u(u + a))` has valuation two, so the lower groups are the whole group at
`0` and `1` and trivial from `2` on. Herbrand's function is the identity on `[0, 1]`, so the
only upper break of `Gal(M/X)` is `1`; the nontrivial character `ψ(−a)` is nontrivial on
`Gal(M/X)^1` and trivial on `Gal(M/X)^(1+ε)`. The finite-image theorem
`Langlands.Ramification.Wintenberger.localAbsoluteUpperFiniteImage` carries this to the absolute
upper groups. For two parameters, `u_c − u_{c'}` solves the equation for `c − c'`, so
`χ_c χ_{c'}⁻¹ = χ_{c−c'}` with `c − c' ≠ 0`. The two weil-conjectures declarations named are at
commit `a25955cde4f85f67bef3149a6efc3efe20c22132`; they, Mathlib's
`Normal.minpoly_eq_iff_mem_orbit` and the Library's `localAbsoluteUpperFiniteImage` report
only `propext`, `Classical.choice` and `Quot.sound` under `#print axioms`. This module's Lean
uses none of them.

## Scope

The statement is in characteristic `p` by nature: `X` is the field of Laurent series over a
finite field. The end traits of `Langlands.Correspondence.Laumon.Traits` are henselian;
`HenselianCompletionGaloisStatement` and `HenselianCompletionRamificationStatement` in
`Langlands.Correspondence.Laumon.Completion` state the comparison of their Galois groups, and
of the inertia and ramification filtrations, with those of the completion `X`. The
Artin–Schreier statement is formulated over the completed field `X`, where the Library's upper
ramification groups are defined.

## Declarations used

The module imports `Langlands.Correspondence.Laumon.SlopeCalculus` and
`Langlands.LocalField.LaurentSeries`. It uses `ladicCharacterLine` of
`Langlands.Correspondence.Laumon.SlopeCalculus`, `slopeSupport` and `ladicSwan` of
`Langlands.Correspondence.Laumon.Slopes`, the Library's `Langlands.LocalField.Laurent.valuativeRel`
and its local-field instance, `IsLadicContinuous` and `IsLadicDefinedOverFiniteExtension`, and
Mathlib's `LaurentSeries`, `HahnSeries.single`, `HahnSeries.C`, `SeparableClosure` and
`AddChar`. It uses no declaration of weil-conjectures. Every declaration of this module depends at
most on `propext`, `Classical.choice` and `Quot.sound`.
