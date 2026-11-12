# Minimality of the conductor and the scaled identity at the conductor level

Author: Worker 5032. This module defines one proposition,
`Langlands.Conductor.ConductorMinimalityStatement` (universes `uF`, `uV`).
It is a statement only: nothing here proves it, and no declaration assumes it.

## Statement

The binders up to and including `IsSelfDual ψ ν` are those of the published
`Langlands.Conductor.EssentialVectorLevelStatement`
([`EssentialStatement`](EssentialStatement.md)), in the same order:

- a field `F : Type uF` with `Field F`, `ValuativeRel F`, `TopologicalSpace F`,
  `IsNonarchimedeanLocalField F`, `T2Space F`, `TotallyDisconnectedSpace F`
  and a Borel measurable structure; any characteristic is allowed and there is
  no `PadicField` restriction;
- `n : ℕ` with the measurable and Borel structures of that statement on
  `GL_(n+1)(F)`, its upper unitriangular subgroup, `GL_1(F)`, its unipotent
  subgroup, and the quotients `LeftUnipotentQuotient n F` and
  `LeftUnipotentQuotient 0 F`;
- `q`, `ψ`, `abv`, `ϖ`, `μ` and `h : IsJacquetNormalization q ψ abv ϖ μ`
  (Jacquet's normalizations, documented in [`Essential`](Essential.md): `q` is
  the residue cardinality, `ϖ` a uniformizer, `abv` the normalized absolute
  value, `ψ` of conductor `O`, `μ` the compatible quotient measure);
- an additive Haar measure `ν` on `F` with `IsSelfDual ψ ν`.

Then for every `V : Type uV` (independent of `uF`) and
`π : Representation ℂ (GeneralLinear ((n + 1) + 1) F) V` with
`IsGeneric ψ (n + 1) π`:

- every `ℓ : glFunctionals ψ (n + 1) π` with `ℓ.val ≠ 0`;
- every polynomial `P : ℂ[X]` with
  `IsCharacterLPolynomial q ψ abv (rankOneQuotientHaar F) 1 π P`;
- every `c : ℂˣ` and `m : ℤ` with
  `IsPairEpsilonFactor q ψ abv ν π (rankOneCharacter 1) (c, m)`;
- every level `u : ℕ` and every vector `v : (coefficientModel π ℓ).toSubmodule`
  with `v ∈ levelFixedVectors (modelRepresentation π ℓ) u`;

both of the following hold:

1. `v ≠ 0 → m ≤ u`;
2. if `u = m`, there is one `C : ℂ` such that for every `x : Fin (n + 1) → ℂˣ`
   the integral `corankOneIntegral ψ abv μ v.val (inverseSphericalWhittaker … x) s`
   converges absolutely (`CorankOneConverges`) for all `s` in some right
   half-plane `a < Re s`, and it agrees on some right half-plane with the
   rational function `C • essentialFactor P x` of `X = q^(-s)`
   (`HasRationalContinuation q`).

The constant `C` is chosen before `x`, so it does not depend on `x`. The rank
is `r = n + 2 ≥ 2`; `n = 0` (rank two) is included. Every level `u ≥ 0` is
included, in particular `u = 0`. The exponent `m` is an integer and is not
truncated to a natural number. With `ℓ` fixed, the second conclusion is
exactly the published `SatisfiesScaledEssentialIdentity q ψ abv μ
h.conductor.1 h.uniformizer P C v.val` of
[`EssentialScaledUniqueness`](EssentialScaledUniqueness.md), written out.

## Source correspondence

H. Jacquet, I. I. Piatetski-Shapiro and J. Shalika, *Conducteur des
représentations du groupe linéaire*, Math. Ann. 256 (1981), 199–214; registered
source `jpss-1981-conductor`, file
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Conducteur des representations du groupe lineaire--1981.pdf`,
SHA-256 `986b06d6c16221fd55f04480604a1b17bf11004a704ab16b78acdd131ae6d49d`
(printed page 199 is PDF page 1). Pages read rendered: printed 208–211
(PDF 10–13) for the notation and Theorem (5.1), and printed 213–214 (PDF 15–16)
for the argument.

The statement is the end of the proof of Theorem (5.1), printed page 213 from
"Soit maintenant `u` un entier `≥ 0` et `W₁` un vecteur de `𝒲(π; ψ)`
invariant sous `K(u)`" to printed page 214, "Enfin si `u = m` la relation
ci-dessus montre que `P` est une constante." The source's notation corresponds
as follows.

- **`K(u)`.** Theorem (5.1)(ii), printed page 211, defines `K_r(a)` for
  `a > 0` as the matrices `(h v; u x)` of `K_r = GL_r(O)` with `h ∈ K_(r-1)`,
  `x ≡ 1 mod 𝔭^a` and `u ≡ 0 mod 𝔭^a`, and sets `K_r(0) = K_r`. The published
  `levelSubgroup F (n + 1) u` ([`Congruence`](Congruence.md)) is the image in
  `GL_(n+2)(F)` of the matrices of `GL_(n+2)(O)` whose last row is
  `(0, ..., 0, 1)` modulo `𝔭^u`; at `u = 0` it is all of `GL_(n+2)(O)`. These
  are the same groups (for `a > 0` the block `h` is automatically invertible
  over `O`). The source's `K(u)`-invariant `W₁ ∈ 𝒲(π; ψ)` is a vector `v` of the
  coefficient model of `ℓ` (the Whittaker model, `coefficientModel π ℓ`) in
  `levelFixedVectors (modelRepresentation π ℓ) u`, the vectors fixed by
  `levelSubgroup F (n + 1) u` under the model representation (right
  translation).
- **`Ψ(X, W₁, X₁, ..., X_(r−1))`.** Printed page 209 defines
  `Ψ(X, W, W') = ∫ W(diag(g, 1)) W'(g) |det g|^(s−1/2) dg` over
  `N_(r−1) \ G_(r−1)`, with `X = q^(-s)`, and takes
  `W' = W(g; X₁, ..., X_(r−1); ψ̄)`, the spherical Whittaker function for `ψ̄`.
  This is `corankOneIntegral ψ abv μ v.val (inverseSphericalWhittaker
  h.conductor.1 h.uniformizer q x)`, whose integrand is
  `W(rankInclusion 1 g) · W'(g) · |det g|^(s − 1/2)` on
  `LeftUnipotentQuotient n F`, with `x` the Satake parameters `X₁, ..., X_(r−1)`.
  The source treats `Ψ` as a formal Laurent series in `X` with coefficients in
  the symmetric Laurent polynomials `S_(r−1)` in the `X_i`, and notes on
  printed page 208, for its identity (4.2)(1), that an identity in `S_(r−1)`
  follows from the analogous identities with nonzero complex numbers `x_i`
  substituted for the `X_i`. The Library works with those specializations, quantifying over every
  `x : Fin (n + 1) → ℂˣ`, and replaces formal series by absolute convergence
  on a right half-plane together with agreement with a rational function of
  `q^(-s)` there. This is the same encoding as the published
  `SatisfiesEssentialIdentity` of [`Essential`](Essential.md).
- **`∏ P_π(X X_i)⁻¹`.** This is `essentialFactor P x =
  ∏ i, P(x_i X)⁻¹`, where `L(s, π) = P_π(q^(-s))⁻¹` is the hypothesis
  `IsCharacterLPolynomial q ψ abv (rankOneQuotientHaar F) 1 π P`, the
  hypothesis also used in the published `IsEssentialVector`. As recorded in
  [`EssentialStatement`](EssentialStatement.md), this is the JPSS factor
  `L(s, π × 1)`; its agreement with the Godement–Jacquet `L(s, π)` of the
  source is a theorem not in the Library.
- **`ε_π(X, ψ) = C X^m`.** Theorem (5.1), display (1), printed page 211,
  defines `m` by this. The statement uses
  `IsPairEpsilonFactor q ψ abv ν π (rankOneCharacter 1) (c, m)`: the epsilon
  factor of `π` against the trivial character of `GL_1(F)` is the monomial
  `c q^(-ms)` (published `epsilonMonomial q c m`), that is `c X^m`. Since `π`
  has rank `n + 2 > 1`, this is the unequal-rank relation. As in
  `EssentialVectorLevelStatement`, it is the JPSS pair factor `ε(s, π × 1, ψ)`,
  and `ν` is self-dual for `ψ`; its agreement with the Godement–Jacquet
  factor of the source is likewise not in the Library.

### The two conclusions

The source argues as follows. `H(0)`-invariance of `W₁` restricts the support:
`W₁(diag(g, 1)) ≠ 0` implies `|α_i(g)| ≤ 1` for `1 ≤ i ≤ r − 1` (cf. its
(3.1)), so in the integral one may assume `|det g| ≤ 1`, the series
`Ψ(X, W₁, X₁, ..., X_(r−1))` has only nonnegative powers of `X`, and the
spherical transform `Ξ(W₁, X₁, ..., X_(r−1))` is a polynomial, which the source
names `P`. Here `Ξ` is defined by (4.2)(4), printed page 209:
`Ξ(W, X X₁, ..., X X_(r−1)) = Ψ(X, W, X₁, ..., X_(r−1)) ∏ P_π(X X_i)`. The
translate `W₂(g) = W̃₁(g a)`, `a = diag(ϖ^(-u), ..., ϖ^(-u), 1)`, is again
`H(0)`-invariant, so `Ξ(W₂)` is a polynomial too, and the functional equation
(4.2)(7) gives, printed page 214,

`(X₁ ⋯ X_(r−1))^u Q(q^(-1) X₁^(-1), ..., q^(-1) X_(r−1)^(-1)) =
C^(r−1) q^(-u(r−1)) (X₁ ⋯ X_(r−1))^m P(X₁, ..., X_(r−1))`

with `Q` a constant multiple of `Ξ(W₂)`.

1. "Si on avait `u < m`, `Q(...)` serait un polynôme en `X₁, ..., X_(r−1)`
   divisible par le produit `X₁ X₂ ⋯ X_(r−1)`, ce qui est absurde. On a donc
   `u ≥ m`." The absurdity uses `W₁ ≠ 0`; this is the first conclusion
   `v ≠ 0 → m ≤ u`. It is also Theorem (5.1)(iii), printed page 211: "Si
   `a ≥ 0` et s'il existe dans `π` un vecteur non nul fixé par `K_r(a)`, alors
   `a ≥ m`."
2. "Enfin si `u = m` la relation ci-dessus montre que `P` est une constante."
   The source's `P` here is the spherical transform `Ξ(W₁)`, not the
   L-polynomial. `Ξ(W₁) = C` constant means, by (4.2)(4),
   `Ψ(X, W₁, X₁, ..., X_(r−1)) = C ∏ P_π(X X_i)⁻¹`, which is the second
   conclusion: one `C` for every `x`, with the Library's `P` the L-polynomial
   `P_π`.

The source continues: "D'après l'unicité dans le théorème (4.1) la fonction
`W₁` est alors un multiple de `W`." The statement stops before this appeal to
the uniqueness clause of Theorem (4.1) (printed page 208), so it contains no
essential vector and no uniqueness. The published
`exists_eq_smul_of_mem_levelFixedVectors` of
[`EssentialScaledUniqueness`](EssentialScaledUniqueness.md) performs that last
step in the Library, from the second conclusion at level `m` and the
uniqueness of the corrected essential vector.

### Range of `u` and `m`

The source writes "`u` un entier `≥ 0`", so `u : ℕ` with `u = 0` included
matches it; at `u = 0` the group is `GL_(n+2)(O)`. The argument above uses no
sign of `m`: the source proves `m ≥ 0` earlier in (5.3), from the dual
comparison, and does not use it here. So `m` stays in `ℤ`. If `m < 0`, the
first conclusion holds trivially and the second is vacuous.

## Why `P` is a hypothesis

The L-polynomial `P` is an input of the source argument (it occurs in the
definition of `Ξ`), not something the argument produces. Existence of the
L-polynomial for every generic `π` over an arbitrary nonarchimedean local field
is a separate result that is not in the Library, so it is assumed, as in the
published `IsEssentialVector`. The hypothesis determines `P` uniquely
(published `IsNormalizedGenerator.unique`), so the statement does not depend
on a choice. For the same reason the epsilon factor `(c, m)` is a hypothesis:
its existence over arbitrary `F` is a separate statement
(`TrivialCharacterEpsilonStatement`).

## Why no essential vector occurs

This part of the source argument concerns an arbitrary `K(u)`-fixed vector `W₁`
and never uses the essential vector `W`: the essential vector only enters in the
final appeal to Theorem (4.1), which is excluded. Keeping it out also keeps the
statement independent of the 1981 existence argument for `W`, which is flawed
and was corrected by Jacquet (2012). Accordingly the statement has no essential
vector, no essential-vector existence or uniqueness, no functional equation, no
last-row support, no mirabolic injectivity, no dual comparison, no multiplicity
one and no conductor theorem among its premises. A proof must supply the
analytic inputs of the source argument over arbitrary nonarchimedean local
fields: the Levi support restriction for `H(0)`-invariant vectors,
polynomiality of the spherical transforms, and the corank-one functional
equation against unramified test functions with the factorization of its
epsilon factor.

## The vector `v = 0`

For `v = 0` the first conclusion is vacuous. The second holds with `C = 0`:
the integrand of `corankOneIntegral` is identically zero (the published
`corankOneIntegral_zero_left` of
[`EssentialConductorAssembly`](EssentialConductorAssembly.md) evaluates the
integral to `0`), so it converges at every
`s`, and `HasRationalContinuation q 0 (0 • essentialFactor P x)` holds because
the zero rational function has denominator `1`. So the statement does not
assert that a nonzero level-`m` fixed vector exists.

## What this statement does not supply

It gives neither essential-vector existence and uniqueness (Jacquet 2012,
Theorem 1) nor the full conductor theorem JPSS (5.1). The further inputs are:

- existence and uniqueness of the corrected essential vector `w` (Jacquet
  2012, Theorem 1); the published `EssentialUniquenessReduction` reduces
  uniqueness to mirabolic restriction injectivity
  (`MirabolicRestrictionInjectivityStatement`);
- that `w` is fixed by `K(m)` and that `m ≥ 0`: the dual comparison
  (`EssentialDualComparisonStatement`, JPSS (5.3)), integral last-row support
  (`EssentialIntegralLastRowSupportStatement`) and mirabolic restriction
  injectivity, combined by the published
  `mem_levelFixedVectors_of_rankInclusion_dual_comparison`
  ([`EssentialDualSetup`](EssentialDualSetup.md));
- existence of `P` and of the epsilon factor `(c, m)` over arbitrary `F`.

Given these, the first conclusion shows that every level below `m` has no
nonzero fixed vector, and the second conclusion at `u = m` with the published
`exists_eq_smul_of_mem_levelFixedVectors` shows that every level-`m` fixed
vector is a multiple of `w`; the published
`isNewvectorConductor_and_finrank_of_essential`
([`EssentialConductorAssembly`](EssentialConductorAssembly.md)) turns this level
line into `IsNewvectorConductor π m` and dimension one.

## Imports

Only the published `Langlands.Representation.Conductor.EssentialStatement`,
whose import closure supplies `IsJacquetNormalization`, `IsGeneric`,
`glFunctionals`, `coefficientModel`, `modelRepresentation`,
`levelFixedVectors`, `IsCharacterLPolynomial`, `rankOneQuotientHaar`,
`IsPairEpsilonFactor`, `rankOneCharacter`, `IsSelfDual`,
`CorankOneConverges`, `corankOneIntegral`, `inverseSphericalWhittaker`,
`HasRationalContinuation` and `essentialFactor`. `Polynomial` is opened for
`ℂ[X]`.
