# The epsilon monomial of a highly ramified twist

Module `Langlands.Representation.RankinSelberg.UniformRankOneTwistEpsilon`.

Authors: Worker 1836. The module builds on Worker 1807's
[UniformRankOneTwistTest](UniformRankOneTwistTest.md), which supplies the test
function, its Fourier support and the dual-side pointwise identity. Worker 1807
also suggested reading the exponent and the constant off the functional equation
at two explicit points, which avoids a separate convergence or uniqueness
argument.

This internal module serves the proof of
[UniformRankOneTwistStatement](UniformRankOneTwistStatement.md). It computes the
exponent and the constant of the Godement–Jacquet epsilon monomial of a
representation `ρ` of `GL_(n+1)(F)` that has a ramified eigenvector. The result is
stated for normalized matrix functional-equation data whose two polynomials are
both `1`; the L-vanishing module
[UniformRankOneTwistLVanishing](UniformRankOneTwistLVanishing.md) shows that the
data of a highly ramified twist have this form.

Everything uses the canonical topology, valuation, Borel structures and
normalized absolute value of the supplied p-adic field `F`, and the Library's
Haar measure `generalLinearHaar` on `GL_(n+1)(F)`. Write `q` for the residue
cardinality, `a(χ)` for the canonical multiplicative conductor exponent of a
quasicharacter `χ`, `j = twistLevel a(χ)`, `K_j` for
`Conductor.principalLevelSubgroup F.Carrier n j`, `Φ = twistedPrincipalFun F χ j`
(the function `1_{1 + ϖ^j M(O)}(y) χ(det y)⁻¹`), and `Φ^` for its Fourier
integral `rectangularFourierIntegral ψ ν Φ`. The spectral variable is
`X = spectralPoint q s = q^(-s)`.

## Definitions

- `twistedDualIntegral F ψ ν n χ ω` is the complex number
  `J = ∫ Φ^(g) · u(g) · |det g|^(n/2) dg` over `GL_(n+1)(F)`, where
  `u = twistedEpsilonWeight F χ ω` is the weight
  `u(g) = ω(g₀₀)⁻¹ χ(g₀₀)^(n+1) χ(det g)⁻¹` (and `0` when `g₀₀ = 0`).
  The integral is the Bochner integral; no convergence is asserted.
- `twistedMatrixEpsilonConstant F ψ ν n χ ω` is
  `J · q^((n+1) a(χ)) / vol(K_j)`, the volume taken for `generalLinearHaar`.

Both depend only on `F`, `ψ`, `ν`, `n`, `χ` and `ω`; they do not depend on any
representation. That independence is what the level-uniform statement needs.

## Results

- `val_mem_principalSet_iff`: for `j > 0`, an invertible `g` has its matrix in
  `principalSet F n j` (that is, in `1 + ϖ^j M(O)`) exactly when `g ∈ K_j`.
- `measureReal_principalLevelSubgroup_ne_zero`: `vol(K_j) ≠ 0`, since `K_j` is
  open and compact.
- `matrixIntegrand_twistedPrincipalTest` and `matrixIntegral_twistedPrincipalTest`:
  if `f(g) = χ(det g) f(1)` for `g ∈ K_j`, then the integrand
  `Φ(g) f(g) |det g|^s` is `f(1)` on `K_j` and `0` elsewhere, for every `s`. So the
  zeta integral is the constant `vol(K_j) f(1)`.
- `matrixIntegral_dual_eq`: suppose that on the set where `Φ^(g) ≠ 0` we have
  `f(ι g) = f(1) u(g)` and `ord(det g) = -N`, where `ι g = (g⁻¹)ᵀ`. Let `Φ̂` be
  any test function equal to `Φ^` pointwise. Then the shifted dual integral
  `∫ Φ̂(g) f(ι g) |det g|^(s + n/2) dg` equals `f(1) · J · X^(-N)` for every `s`.
- `epsilon_eq_of_coefficient`: let `ρ` carry
  `Padic.NormalizedMatrixFunctionalEquationData F ψ ν ρ 1 1 c a`. Let `f` be a
  bi-smooth matrix coefficient of `ρ` with `f(1) ≠ 0` and `f(g) = χ(det g) f(1)` on
  `K_j`, which satisfies the pointwise law of `matrixIntegral_dual_eq` with
  `N = (n+1) a(χ)`. Then `a = (n+1) a(χ)` and
  `c = twistedMatrixEpsilonConstant F ψ ν n χ ω`.
- `twistedMatrixEpsilon`: let `ρ` be smooth with central character `ω`, and let
  `ψ` have conductor exponent `0`. Let `1 ≤ m'` and `2m' ≤ a(χ)`, and let
  `w ≠ 0` satisfy `ρ(y) w = χ(det y) w` for all `y ∈ K_(m')`. If
  `Padic.NormalizedMatrixFunctionalEquationData F ψ ν ρ 1 1 c a` holds, then
  `a = (n+1) a(χ)` and `c = twistedMatrixEpsilonConstant F ψ ν n χ ω`.

## Proof

For the original side, `g ∈ K_j` has `|det g| = 1` and `Φ(g) = χ(det g)⁻¹`, so the
integrand is `χ(det g)⁻¹ χ(det g) f(1) = f(1)`. Off `K_j` the test vanishes, by
`val_mem_principalSet_iff`. The integral of an indicator of a constant is the
volume times the constant.

For the dual side, the integrand vanishes where `Φ^(g) = 0`. Elsewhere,
`f(ι g) = f(1) u(g)`, and `ord(det g) = -N` turns `|det g|^s` into `X^(-N)`
(`Padic.determinantWeight_shift_spectral`). The factor `f(1) X^(-N)` is constant
in `g` and comes out of the integral.

For `epsilon_eq_of_coefficient`, apply the data to the test
`twistedPrincipalTest F n χ` and to `f`. The data give the convergence half-planes
of both integrals and a Fourier partner `Φ̂`, equal to `Φ^` pointwise. By the two
integral computations, the rational functions `R = A` and `RD = D X^(-N)` are
rational values of the original and dual integrals at every `s`, with
`A = vol(K_j) f(1) ≠ 0` and `D = f(1) J`. With both polynomials `1`, the functional
equation reads `RD(q^(-(1-s))) = c X^a R(X)`. Since `q^(-(1-s)) = (q X)⁻¹`, this is
`D (q X)^N = c X^a A` for every `s`. At `s = 0` (`X = 1`) it gives `D q^N = c A`.
At `s = -1` (`X = q`) it gives `D q^(2N) = c q^a A = D q^N q^a`. Here `D q^N = c A`
is nonzero, so `q^N = q^a`, and `q > 1` gives `a = N`. Then
`c = D q^N / A = J q^N / vol(K_j)`, after cancelling `f(1)`.

For `twistedMatrixEpsilon`, the Library's
`exists_smoothDual_apply_ne_zero_of_compact_cofinal` gives a smooth functional `ℓ`
with `ℓ(w) ≠ 0`. Take the bi-smooth coefficient `f(g) = ℓ(ρ(g) w)`. The central
character and the eigenvector property give `f(z y) = ω(z) χ(det y) f(1)` for
scalars `z` and `y ∈ K_(m')`. Since `m' ≤ j`, so that `K_j ⊆ K_(m')`, this also
gives `f(g) = χ(det g) f(1)` on `K_j`. Worker 1807's
`UniformTwist.coefficientIota_eq_of_fourierIntegral_ne_zero` supplies the dual
pointwise law with `N = (n+1) a(χ)`, and `epsilon_eq_of_coefficient` concludes.

## Provenance

This is a derived argument adapted from Jacquet–Shalika, *A lemma on highly
ramified ε-factors*, Math. Ann. 271 (1985), §§2.4–2.5 (printed pages 320–322;
registered source `jacquet-shalika-1985-ramified-factors`). JS85 derive their
identity §2.4 (4) from the Godement–Jacquet theory (Godement–Jacquet, *Zeta
Functions of Simple Algebras*, 1972, Lemma 5.3, p. 59; registered source
`godement-jacquet-1972-zeta-simple-algebras`). In §2.5 they evaluate it on a test
built from a matrix coefficient `f` with `f(e) ≠ 0`, bi-invariant under some
`K_i`. They use the level `j = ⌈k/2⌉` (§2.5 (2)) and find that the transform is
`f(g) χ(det g) |det g|^(-r)` times the constant
`ε(χ, ω, r) = ω⁻¹(c) χ⁻¹(c^r) η(χ, r)` (§2.5 (10)–(12)). This constant depends only
on `χ`, the central character `ω` and `r`.

The implemented proof applies the same idea directly to the Library's
Godement–Jacquet functional equation for normalized matrix data. It uses the test
`1_{K_j} χ⁻¹(det)` on full matrices and one coefficient `f` that is a
`χ ∘ det`-eigenfunction on the right, not a bi-invariant one. The original integral
is the constant `vol(K_j) f(1)`, and the dual integral is the constant `f(1) J`
times `q^((n+1) a(χ) s)`. The constant `twistedMatrixEpsilonConstant` is defined
here as the explicit value this computation produces. It is not claimed to agree
term by term with JS85's `ε(χ, ω, r)`, since the two functional equations and their
normalizations differ. The proof uses only that it depends on `F`, `ψ`, `ν`, `n`,
`χ` and `ω` alone.
