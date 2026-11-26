# Fourier transforms of nilpotent orbital distributions are locally integrable

The module `Langlands.HarmonicAnalysis.UnitConjugation.NilpotentOrbitalFourierRegularityStatement`
states, as the proposition
`Langlands.HarmonicAnalysis.NilpotentOrbitalFourierRegularityStatement.{u, v}`, the
specialization of Harish-Chandra's Theorem 4.4 to orbital distributions of nilpotent elements:
on the same algebra data as `LieAlgebraFourierRegularityStatement`, the Fourier transform of the
orbital distribution of a nilpotent element, for compatible quotient measures and convergent
orbital integrals, is given by a locally integrable function. The statement is **not** proved
here. The module proves that `LieAlgebraFourierRegularityStatement` implies it, and computes the
orbit of `0`.

## Statement

`NilpotentOrbitalFourierRegularityStatement.{u, v}` quantifies over

- the algebra data of `LieAlgebraFourierRegularityStatement`: a nonarchimedean local field
  `F : Type u` of characteristic zero; a finite-dimensional semisimple `F`-algebra `A : Type v`
  with its module topology and Borel σ-algebra; `ψ : UnitaryAdditiveCharacter F`;
  `B : LinearMap.BilinForm F A` with `hB : IsInvariantPairing B`; `μ : AdditiveHaarMeasure A`;
- a Borel σ-algebra on `Aˣ` (`[MeasurableSpace Aˣ] [BorelSpace Aˣ]`, for the topology of `Aˣ`
  as units of the topological ring `A`) and one on the coset space
  `LeftQuotient (conjugationCentralizer N)`; the centralizer carries the induced σ-algebra;
- a nilpotent `N : A` (`IsNilpotent N`);
- the retained Haar data: a Haar measure `μG` on `Aˣ` (`μG.IsHaarMeasure`), a Haar measure `μH`
  on the centralizer `C = conjugationCentralizer N` that is also right-invariant
  (`μH.IsHaarMeasure`, `μH.IsMulRightInvariant`; centralizers are unimodular, Harish-Chandra
  p. 2), and a quotient measure `ν` on `C \ Aˣ` with
  `QuotientIntegration.IsCompatible C μG μH ν` (nonzero, regular, invariant under right
  translations, with the Weil integral formula `∫_{C \ Aˣ} ∫_C f(h g) dμH dν = ∫ f dμG` for
  compactly supported continuous `f`);
- the convergence premise `hconv : OrbitalIntegralConverges N ν`: every test integral
  `∫_{C \ Aˣ} f(g⁻¹ N g) dν` converges absolutely.

The claim: there is `Θ : A → ℂ` with `LocallyIntegrable Θ μ.measure` and

`distributionFourier ψ hB.isSymm hB.nondegenerate μ (orbitalDistribution N ν hconv) f =
  ∫ X, Θ X * f X ∂μ.measure`

for every Schwartz–Bruhat function `f`; the left side is `μ̂_N(f) = μ_N(f̂)` for the orbital
distribution `μ_N(f) = ∫_{C \ Aˣ} f(g⁻¹ N g) dν(C g)`
(`Langlands.HarmonicAnalysis.UnitConjugation.OrbitalDistribution`).

## Hypotheses and the role of compact support modulo conjugation

`LieAlgebraFourierRegularityStatement.nilpotentOrbital` (proved) shows that
`LieAlgebraFourierRegularityStatement.{u, v}` implies
`NilpotentOrbitalFourierRegularityStatement.{u, v}`, and its proof shows what each hypothesis
does:

- the orbital distribution needs the convergence premise `hconv` to be a linear functional at
  all (`orbitalDistribution`);
- compatibility of `ν` gives its right invariance, which makes `μ_N` conjugation-invariant
  (`orbitalDistribution_isConjugationInvariant`);
- `μ_N` is supported in the closure of the orbit of `N`, which is the closure of the saturation
  of the compact set `{N}` (`orbitalDistribution_mem_supportedOn`); so
  `μ_N ∈ J({N})` (`orbitalDistribution_mem_invariantSupportedIn_of_isCompatible`), and
  Theorem 4.4 applies with `ω = {N}` (`isCompact_singleton`).

The compact set `ω` of Theorem 4.4 thus serves as the support of `μ_N` modulo conjugation: a
single orbit is the saturation of a point. The reduction does not use nilpotency, the Haar
property of `μG` or `μH`, or the semisimplicity of `A` beyond passing them to Theorem 4.4; the
same argument applies to every orbit, as Harish-Chandra remarks. Nilpotent orbits are the case
used in the character expansions: the conjugates of a nilpotent element are nilpotent
(`isNilpotent_of_mem_conjugationSaturation`).

`distributionFourier_orbitalDistribution_zero` (proved) treats `N = 0` directly: the orbit is
`{0}`, `μ_0(f) = ν(C \ Aˣ) f(0)` (`orbitalDistribution_zero_apply`) and
`f̂(0) = ∫ f dμ`, so `μ̂_0(f) = ∫ ν(C \ Aˣ) f(X) dμ(X)`, with the constant function
`ν(C \ Aˣ)` as density. Its hypotheses are only the Fourier data (symmetric nondegenerate `B`)
and the convergence premise.

## Sources

Harish-Chandra, *Admissible invariant distributions on reductive p-adic groups*, with notes by
S. DeBacker and P. J. Sally, Jr., University Lecture Series 16, AMS, 1999, source ID
`harish-chandra-1999-admissible-invariant-distributions` (PDF page = printed page + 15),
Introduction, printed pp. 2–3 (PDF pp. 17–18): the positive measure
`μ_O(f) = ∫_{G/C_G(X₀)} f(x.X₀) dx*` on an orbit, well defined by Deligne and Ranga Rao, "It
follows from Theorem 4.4 (Theorem 3) that `μ̂_O` is a function"; the nilpotent orbits, finite in
number, with `{0}` among them; Theorem 5.11 (Theorem 4) and Theorem 16.2 (Theorems 5 and 20),
the expansions in the `μ̂_O` for nilpotent `O`. Theorem 4.4 itself is on printed p. 31 (PDF
p. 46).

Clozel, *Characters of non-connected, reductive p-adic groups*, Canad. J. Math. 39 (1987),
source ID `clozel-1987-nonconnected-characters` (PDF page = printed page − 148), §3.3, Theorem 3,
printed p. 154 (PDF p. 6): near a semisimple `γ`, the character is `Σ c_O ν̂_O(Y)` over the
nilpotent orbits `O` of the connected centralizer `M` in its Lie algebra `m`, with `ν_O` the
invariant measure on `O` and `ν̂_O` its Fourier transform; §3.4, printed pp. 155–156 (PDF
pp. 7–8): the Fourier transform by `χ(B(X, Y))`, and the use of Harish-Chandra's theorem for
invariant distributions with compact support modulo conjugation.

In Harish-Chandra's convention the orbit is `G/C_G(X₀)` with `x ↦ x.X₀`; here it is the
Library's left coset space `C \ Aˣ` with `g ↦ g⁻¹ N g`, carried to Harish-Chandra's by
`C g ↦ g⁻¹ C`. The orbit measures are determined up to a positive constant, which the retained
Haar data `μG`, `μH` and the compatibility of `ν` fix.

## Not stated here

The convergence of nilpotent orbital integrals (Deligne–Ranga Rao), the existence of compatible
quotient measures, the expansion of Theorem 5.11 and the linear independence of the `μ̂_O`.
