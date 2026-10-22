# Pole regions of Weil–Deligne L-polynomials

This module states the Weil-group half, part (i), of Henniart (1986),
Proposition 4.5. Under either of two hypotheses on a pair of local
Weil–Deligne parameters `σ, σ'`, the L-polynomial of `σ ⊗ σ'` and the
reflected L-polynomial of `σ^∨ ⊗ σ'^∨` have no common zero. Henniart's
Lemma 4.4 then separates L- and epsilon-factors from an equality of gamma
factors; the published `Langlands.Global.GammaPolynomialSeparationStatement`
(in `Langlands/Global/Factors/SeparationStatement`) is that algebraic step, and
its no-common-zero hypothesis has exactly the form concluded here. Everything is
stated over the actual local Weil group of a p-adic field and its actual
Weil–Deligne parameters. The module introduces no substitute types and no
assumed local-factor theorems.

## Actual objects

All objects are the published local Weil-group constructions of
`Langlands.Weil.Local`, for a prime `p` and a p-adic field
`F : PadicField.{u} p`:

- `localWeilGroup F`, its inertia subgroup `localInertia F`, and the chosen
  geometric Frobenius lift `localGeometricFrobenius F` of geometric degree one.
- `localNormCharacter F`, written `ν` below. It is the character
  `w ↦ q^(-deg w)`, where `q` is the residue cardinality of the canonical
  realization of `F`, so `ν(Φ) = q⁻¹` at a geometric Frobenius `Φ`. Henniart
  §2.2 normalizes reciprocity so that geometric Frobenius elements correspond to
  uniformizers, and writes `α_E = |·|_E`. Hence `ν` is his `α_F` pulled back
  to the Weil group, and equally Tate's `w ↦ ‖w‖` from (4.1).
- `LocalOpenInertiaWeilObjects F`: finite-dimensional complex representations of
  the Weil group whose kernel meets inertia in an open subgroup. Henniart
  works with this convention, following Tate (4.1.2)(a).
- `LocalParameterObjects F`: actual Weil–Deligne pairs `(ρ, N)` with open
  inertia kernel and arbitrary nilpotent monodromy satisfying
  `ρ(w) N ρ(w)⁻¹ = ν(w) N`.
- `localZeroMonodromyParameter F A`: the pair `(A, 0)`.
- `localParameterTensor`: the tensor pair with monodromy `N ⊗ 1 + 1 ⊗ N'`.
  `localParameterDual`: the full linear dual with negative-transpose monodromy,
  that is, the contragredient.
- `localBlock F ρ m`: the block `ρ ⊗ Sp(m)`. Its space is `ρ ⊗ ℂ^m`, the Weil
  group acts on the `j`-th basis line by `ν^j`, and `N` raises the index. This
  is Tate's `Sp(n)` of (4.1.4). The kernel of `N` is the top line `ρ ν^(m-1)`.
- `WeilDeligneRepresentation.directSum` over `Fin k` and
  `WeilDeligneRepresentation.Equiv`, the actual isomorphisms of pairs (linear
  equivalences intertwining both the Weil action and the monodromy).
- `FiniteRepresentation.twist`, `IsUnitary` (an invariant Hermitian inner
  product exists), `IsIsomorphic`, and `IsIrreducible` (nonzero, with no
  invariant subspaces other than `0` and the whole space).

## Helper definitions

In namespace `Langlands.Global.WeilPoleRegion`:

- `residueCardinality F` is the residue cardinality `q` of
  `F.canonicalTopologicalData`, the same `q` used by `localNormCharacter`.
- `lPolynomial F σ` is the published
  `LocalFactor.WeilDeligne.eulerPolynomial` of `σ` at actual inertia and the
  chosen geometric Frobenius:
  \[
    P_\sigma(X) = \det\bigl(1 - X\,\Phi \mid (\ker N)^{I}\bigr),
  \]
  so that `L(σ, s) = P_σ(q^(-s))⁻¹`. This is Tate (4.1.6), Henniart §2.3
  (`L(σ) = P_σ(q^(-s))⁻¹`, `P_σ(0) = 1`). The polynomial does not depend on the
  choice of Frobenius lift, because inertia acts trivially on `(ker N)^I`.
- `HasNoReflectedCommonZero F P Pdual` says that no nonzero `z` satisfies
  both `P(z) = 0` and `Pdual(q⁻¹ z⁻¹) = 0`. With `Pdual = P_{σ^∨}` this says
  that `P_σ` and Henniart's `P̃_σ(X) = P_{σ^∨}(q⁻¹X⁻¹)` of §4.4 have no common
  zero. Zero is excluded because `P̃_σ` is a polynomial in `X⁻¹`, and
  `P_σ(0) = 1` in any case.
- `IsEssentiallyUnitary F A` says that some continuous character
  `χ : localWeilGroup F →ₜ* ℂˣ` makes `χ ⊗ A` unitary. This is Henniart's
  definition in §4.6 ("there is a character `χ` such that `χΣ` is unitary"),
  where characters are continuous by §2.1.
- `AreJuxtaposed F ρ m ρ' m'` says `ρ' ≅ ν^m ρ` or `ρ ≅ ν^(m') ρ'`. This is
  Henniart §2.4 b): `ρ ⊗ sp(r)` and `ρ' ⊗ sp(r')` are juxtaposed if
  `ρ' = α^r ρ` or `ρ = α^(r') ρ'`.

## The statements

`Langlands.Global.EssentiallyUnitaryPoleRegionStatement` quantifies a prime `p`,
a p-adic field `F`, and two open-inertia Weil representations `A`, `B`, both
essentially unitary. With `σ = (A, 0)` and `σ' = (B, 0)` it concludes

\[
  \text{no } z \neq 0 \text{ with }
  P_{\sigma\otimes\sigma'}(z) = 0 = P_{\sigma^\vee\otimes\sigma'^\vee}(q^{-1}z^{-1}).
\]

`Langlands.Global.NonJuxtaposedPoleRegionStatement` quantifies a prime `p`,
a p-adic field `F`, a natural number `k`, irreducible open-inertia Weil
representations `ρ_i` and integers `n_i ≥ 1` for `i : Fin k`, such that the
blocks `ρ_i ⊗ Sp(n_i)` and `ρ_j ⊗ Sp(n_j)` are not juxtaposed for `i ≠ j`.
It also quantifies a parameter `σ` isomorphic, as a Weil–Deligne pair, to
`⊕_i ρ_i ⊗ Sp(n_i)`, and an irreducible open-inertia Weil representation `B`.
With `σ' = (B, 0)` it reaches the same conclusion.

`Langlands.Global.WeilPairPoleRegionStatement` is the conjunction of the two.
All variables are quantified inside the targets. Universe levels `u` (the
field), `v` (the carrier of `σ`) and `w` (the carrier of `σ'`) are
independent.

## Why the statement holds

The following is a guide for the later proof, re-derived from Henniart's §4.7
in the Library's conventions.

**First case.** Put `V = A ⊗ B` and `V' = A^∨ ⊗ B^∨`. Both tensor pairs have
zero monodromy, so `P_{σ⊗σ'}(X) = det(1 - XΦ | V^I)` and
`P_{σ^∨⊗σ'^∨}(X) = det(1 - XΦ | V'^I)`. The characters `χ_A`, `χ_B` give
unitary twists `χV` and `χ⁻¹V'` with `χ = χ_A χ_B`, since the duals of the
invariant inner products are invariant. Because `I` is normal, `V^I` is stable
under `Φ`. On it `Φ` acts by `χ(Φ)⁻¹ (χV)(Φ)`, and a unitary operator has
unimodular eigenvalues on an invariant subspace. So every eigenvalue of `Φ` on
`V^I` has modulus `M = |χ(Φ)|⁻¹`, and likewise every eigenvalue on `V'^I` has
modulus `M⁻¹`. The zeros of `P_{σ⊗σ'}` are the inverse eigenvalues, of modulus
`M⁻¹`. A zero `z` of the reflected dual polynomial has `q⁻¹z⁻¹ = λ⁻¹` for an
eigenvalue `λ` on `V'^I`, so `|z| = q⁻¹M⁻¹`. Since `q > 1`, the two sets are
disjoint. Henniart argues instead with `|a_i| q^((1-n_i)/2)` independent of `i`,
citing his 2.4 (7).

**Second case.** `σ ⊗ σ'` is isomorphic to `⊕_i (ρ_i ⊗ B) ⊗ Sp(n_i)`. The
monodromy kernel of the `i`-th summand is `(ρ_i ⊗ B) ν^(n_i-1)`. By Henniart
2.4 (8), the zeros of `P_{ρ_i⊗B}` are `χ(Φ)⁻¹` for the unramified characters
`χ` with `ρ_i ≅ χ B^∨`. Hence the zeros of `P_{σ⊗σ'}` are
`(χ(Φ) q^(1-n_i))⁻¹`. The dual block `(ρ_j ⊗ Sp(n_j))^∨` has monodromy kernel
`ρ_j^∨` (the dual of the cokernel line `e_0`; compare Henniart (5),
`sp(r)^∨ = α^(1-r) sp(r)`). So the zeros of the reflected dual polynomial are
`ξ(Φ)⁻¹ q⁻¹` for unramified `ξ` with `ρ_j ≅ ξ B^∨`. A common zero forces
`ξ(Φ) = χ(Φ) ν(Φ)^(n_i)`, hence `ξ = χ ν^(n_i)` and `ρ_j ≅ ν^(n_i) ρ_i`. For
`i ≠ j` the blocks are then juxtaposed. For `i = j`, taking determinants gives
`ν^(n_i dim ρ_i) = 1`, which is impossible because `ν(Φ) = q⁻¹` has infinite
order and `n_i ≥ 1`. This is Henniart's argument, which concludes with
`α^(n_i) ρ_i = ρ_j`.

## Provenance and specializations

The source result is Henniart (1986), Proposition 4.5(i), printed p.160, with
its proof in §4.7, printed pp.161-162: "Assume that `σ` and `σ'` are
essentially unitary, or that `σ'` is irreducible and `σ` is a sum of
indecomposables no two of which are juxtaposed. Then `P_{σ⊗σ'}` and
`P̃_{σ⊗σ'}` have no common zero." Here `P̃_{σ⊗σ'}` is the reflected polynomial
of `(σ⊗σ')^∨`. The formalization uses `σ^∨ ⊗ σ'^∨` instead, which is isomorphic
as a Weil–Deligne pair. In finite dimension the canonical isomorphism
`(V ⊗ W)^* ≅ V^* ⊗ W^*` intertwines the Weil actions and the negative-transpose
monodromies, and isomorphic pairs have the same L-polynomial. The formalization
makes the following documented choices.

- **p-adic fields.** Henniart allows any nonarchimedean local field. The
  Library's local Weil groups are constructed over `PadicField`, that is,
  finite extensions of `ℚ_p`. That characteristic-zero case is what this module
  states.
- **First case with zero monodromy.** The first hypothesis is stated for
  `σ = (A, 0)` and `σ' = (B, 0)`. Henniart states the definition of essential
  unitarity only for Weil-group representations: in §4.6, for global ones,
  `χΣ` is unitary for some character `χ`. §§2.2-2.4 give no definition for
  pairs with nonzero monodromy. For a general `σ`, his §4.7 uses only the
  consequence that `|a_i| q^((1-n_i)/2)` is independent of `i`. His application,
  the Corollary of Proposition 4.5 via Lemma 4.6, needs only the local
  restrictions of global Weil-group representations, which have zero
  monodromy.
- **Irreducible `σ'`.** Henniart's irreducible elements of the
  Weil–Deligne set are irreducible Weil representations with `N = 0`, by
  Tate (4.1.5): `ker N` is stable, so an irreducible pair has `N = 0`. Thus
  `σ' = (B, 0)` with `B` irreducible.
- **Sums of indecomposables.** By Henniart §2.4 b) and Tate (4.1.5), the
  indecomposables are `ρ ⊗ sp(r)` with `ρ` irreducible and `r ≥ 1`. "A sum of
  indecomposables" is made explicit as an isomorphism of pairs
  `σ ≅ ⊕_{i : Fin k} ρ_i ⊗ Sp(n_i)` with `n_i ≥ 1` and `ρ_i` irreducible.
  The order of the summands is immaterial, and multiplicities are allowed.
- **"No two juxtaposed".** This is required for distinct indices `i ≠ j`. A
  block is never juxtaposed with itself, by the determinant argument above, so
  nothing is lost.
- **Frobenius.** The polynomial is computed at the Library's chosen geometric
  Frobenius lift, which matches Tate (4.1.6) and Henniart's normalization. Any
  other lift gives the same polynomial.
- **Semisimplicity.** Henniart's representations are semisimple (§2.3). The
  first case needs no such hypothesis, because a unitarizable twist is
  automatically semisimple. In the second case the explicit block decomposition
  supplies it.

The Weil–GL comparison and the GL-side part (ii) of Proposition 4.5
(essentially tempered or generic representations) are not stated here.
Part (ii) needs Rankin–Selberg pair L-factors on the GL side.

## Original sources

Guy Henniart, *On the local Langlands conjecture for GL(n): the cyclic case*,
Annals of Mathematics (2) 123 (1986), 145-203. Registered source:
`henniart-1986-cyclic`. Printed page `p` is PDF page `p - 143`.

- §2.1, printed p.149 (PDF p.6): characters are continuous.
- §2.2, printed p.150 (PDF p.7): normalized absolute value `α_E`, and
  reciprocity sending geometric Frobenius to uniformizers.
- §2.3, printed p.150 (PDF p.7): `L(σ) = P_σ(q^(-s))⁻¹` and the
  contragredient.
- §2.4 b)-c), printed p.151 (PDF p.8): indecomposables `ρ ⊗ sp(r)`,
  juxtaposition, (5)-(7), and (8) `L(ρ⊗ρ') = ∏ L(χ)`.
- §4.4, printed p.159 (PDF p.16): `P̃_τ(X) = P_{τ^∨}(q⁻¹X⁻¹)` and the
  separation lemma.
- §4.5 Proposition (i), printed p.160 (PDF p.17).
- §4.6 Lemma, printed pp.160-161 (PDF pp.17-18): essential unitarity.
- §4.7, printed pp.161-162 (PDF pp.18-19): proof of (i).

John Tate, *Number theoretic background*, in *Automorphic Forms,
Representations and L-Functions*, Proc. Sympos. Pure Math. 33, Part II (1979),
3-26. Registered source: `tate-1979-number-theoretic-background`. (4.1),
(4.1.2), (4.1.4)-(4.1.6), printed pp.19-21 (PDF pp.28-30 of the Part II
volume): `‖Φ‖ = q⁻¹`, the Weil–Deligne convention, `Sp(n)`, the
indecomposables, and `L(V, s) = det(1 - Φ q^(-s) | (ker N)^I)⁻¹`.

## Dependencies and acceptance boundary

The module imports the published `Langlands.Weil.Local.ParameterOperations`,
`Langlands.LocalFactor.WeilDeligne` and `Langlands.WeilDeligne.DirectSum`
(Library commit `f5f825f7`). The closing declaration
`Langlands.Global.WeilPairPoleRegionStatement` is a proposition definition. No
theorem is proved here, and no axioms, instances or hypotheses equivalent to the
conclusion are introduced.
