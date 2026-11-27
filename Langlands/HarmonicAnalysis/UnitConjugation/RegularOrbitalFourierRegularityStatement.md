# Fourier transforms of regular orbital distributions are locally integrable

The module `Langlands.HarmonicAnalysis.UnitConjugation.RegularOrbitalFourierRegularityStatement`
states, as the proposition `Langlands.HarmonicAnalysis.RegularOrbitalFourierRegularityStatement.{u, v}`,
the local summability part of Harish-Chandra's Theorem 1.1 for the Lie algebra `A` of the unit
group `Aˣ` of a finite-dimensional semisimple algebra over a nonarchimedean local field of
characteristic zero: the Fourier transform of the orbital distribution of a regular element is
given by a locally integrable function. The statement is **not** proved here.

## Statement

`RegularOrbitalFourierRegularityStatement.{u, v}` quantifies over

- the algebra data of `LieAlgebraFourierRegularityStatement`: a nonarchimedean local field
  `F : Type u` of characteristic zero; a finite-dimensional semisimple `F`-algebra `A : Type v`
  with its module topology and Borel σ-algebra; `ψ : UnitaryAdditiveCharacter F`;
  `B : LinearMap.BilinForm F A` with `hB : IsInvariantPairing B`; `μ : AdditiveHaarMeasure A`;
- a Borel σ-algebra on `Aˣ` (`[MeasurableSpace Aˣ] [BorelSpace Aˣ]`) and one on the coset
  space `LeftQuotient (conjugationCentralizer X)`;
- a regular `X ∈ regularSet F A` (Harish-Chandra's `g'`, defined in
  `Langlands.HarmonicAnalysis.UnitConjugation.RegularSet` by `η(X) ≠ 0`);
- the Haar data of `NilpotentOrbitalFourierRegularityStatement`, for the centralizer
  `C = conjugationCentralizer X` of `X` in `Aˣ`: a Haar measure `μG` on `Aˣ`, a Haar measure `μH`
  on `C` that is also right-invariant, and a quotient measure `ν` on `C \ Aˣ` with
  `QuotientIntegration.IsCompatible C μG μH ν`;
- the convergence premise `hconv : OrbitalIntegralConverges X ν`.

The claim: there is `Θ : A → ℂ` with `LocallyIntegrable Θ μ.measure` and

`distributionFourier ψ hB.isSymm hB.nondegenerate μ (orbitalDistribution X ν hconv) f =
  ∫ Y, Θ Y * f Y ∂μ.measure`

for every Schwartz–Bruhat function `f`: `μ̂_X(f) = μ_X(f̂) = ∫ Θ f dμ`, where
`μ_X(f) = ∫_{C \ Aˣ} f(g⁻¹ X g) dν(C g)` and `f̂(Y) = ∫ ψ(B(Y, Z)) f(Z) dμ(Z)`.

The statement has the form of `NilpotentOrbitalFourierRegularityStatement` with the nilpotent
element replaced by a regular one.

## Source

Harish-Chandra, *Admissible invariant distributions on reductive p-adic groups*, with notes by
S. DeBacker and P. J. Sally, Jr., University Lecture Series 16, AMS, 1999, source ID
`harish-chandra-1999-admissible-invariant-distributions` (PDF page = printed page + 15):

- Introduction, printed p. 2 (PDF p. 17): the invariant form `B`, the character `χ ≠ 1`, the
  Haar measure `dX`, `f̂(Y) = ∫ χ(B(Y, X)) f(X) dX`, `η` and `g'`.
- §1, printed p. 5 (PDF p. 20): for a Cartan subalgebra `h` with `h' = h ∩ g'` and `A` the split
  component of the corresponding Cartan subgroup, `φ_f(H) = |η(H)|^{1/2} ∫_{G/A} f(x.H) dx*`.
  "Fix an element `H₀` in `h'`." Theorem 1.1 (Theorem 8): "The distribution `f ↦ φ_{f̂}(H₀)`
  for `f ∈ D` is a locally summable function on `g` which is locally constant on `g'`. Let `F`
  denote this function. Then `|η|^{1/2} F` is locally bounded on `g`." The local summability
  is proved in §1 (completed on printed p. 13); Remark 4.5 (printed p. 32) returns to the
  local boundedness.

Correspondence with the statement:

- `G = Aˣ`, `g = A` with the adjoint action `X ↦ u X u⁻¹`. A regular `X ∈ g'` lies in the
  Cartan subalgebra `h` that is its centralizer in `g`, and `X ∈ h'`; take `H₀ = X`.
- The centralizer `C` of `X` in `Aˣ` is the Cartan subgroup of `h`, and its split component
  `A_h` has compact quotient `C/A_h`, so
  `φ_{f̂}(X) = |η(X)|^{1/2} vol(C/A_h) μ_X(f̂)` with a positive constant factor. A locally
  summable `F` for `f ↦ φ_{f̂}(X)` gives `Θ = F / (|η(X)|^{1/2} vol(C/A_h))` for
  `f ↦ μ_X(f̂)`; changing `ν`, `μ` or the choices of `ψ` and `B` admitted by the source changes
  `Θ` accordingly, and the source theorem holds for each such choice.
- The Library's orbital distribution integrates over the left coset space `C \ Aˣ`; the map
  `C g ↦ g⁻¹ C` identifies it with Harish-Chandra's `G/C`
  (`Langlands.HarmonicAnalysis.UnitConjugation.OrbitalDistribution`).
- The Library's `LocallyIntegrable` (integrable on a neighbourhood of every point) is local
  summability on the locally compact space `A`.

Clauses not stated here: the local constancy of `Θ` on `g'` and the local boundedness of
`|η|^{1/2} Θ`.

In Harish-Chandra's proof of Theorem 4.4 (1) (§4, printed p. 31, PDF p. 46), the
Fourier transform of a distribution in `J(ω)` agrees, on the test functions supported in a
compact open set, with a finite linear combination of Fourier transforms of regular orbital
integrals, and Theorem 1.1 makes each of these a locally summable function.
