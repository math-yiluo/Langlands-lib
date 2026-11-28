# The space `D₀` is stable under the Fourier transform

The module `Langlands.HarmonicAnalysis.UnitConjugation.RegularOrbitalFourierStabilityStatement`
states, as `Langlands.HarmonicAnalysis.LieAlgebraRegularOrbitalFourierStabilityStatement.{u, v}`,
the Fourier half of Harish-Chandra's Lemma 3.16 for the Lie algebra `A` of the unit group of a
finite-dimensional semisimple algebra over a nonarchimedean local field of characteristic zero.
The statement is **not** proved here.

## Statement

For every nonarchimedean local field `F : Type u` of characteristic zero, every
finite-dimensional semisimple `F`-algebra `A : Type v` with its module topology (and Borel
σ-algebras on `A` and on `Aˣ`), every nontrivial continuous unitary additive character `ψ` of
`F` (`UnitaryAdditiveCharacter F`), every bilinear form `B` with `IsInvariantPairing B`
(symmetric, nondegenerate, invariant under conjugation by units), every additive Haar measure
`μ` on `A` and every Schwartz–Bruhat function `f`:

`RegularOrbitalVanishing F A f → RegularOrbitalVanishing F A (pairingFourierSB ψ hB.isSymm
hB.nondegenerate μ f)`,

where `pairingFourierSB` is the Library's Fourier transform `f̂(Y) = ∫ ψ(B(Y, X)) f(X) dμ(X)`
(module `Langlands.HarmonicAnalysis.UnitConjugation.PairingFourier`) and
`RegularOrbitalVanishing F A f` is the condition `f ∈ D₀`: all orbital integrals of `f` over
regular orbits vanish, for all compatible quotient measures with convergent orbital integrals
(module `Langlands.HarmonicAnalysis.UnitConjugation.RegularOrbitalVanishing`).

## Source

Harish-Chandra, *Admissible invariant distributions on reductive p-adic groups*, with notes by
S. DeBacker and P. J. Sally, Jr., University Lecture Series 16, AMS, 1999, source ID
`harish-chandra-1999-admissible-invariant-distributions` (PDF page = printed page + 15),
§3.5, printed p. 28 (PDF p. 43), Lemma 3.16 (Lemma 8): "Suppose `f ∈ D₀` and `t ∈ Ω^×`.
Then `f̂` and `f_t` are also in `D₀`." The statement here is the assertion about `f̂`, for
every choice of `ψ`, `B` and the Haar measure entering `f̂`. Harish-Chandra's proof writes
`φ_{f̂}(H₀)` as the integral of `f` against the locally summable function representing the
Fourier transform of the orbital integral at `H₀` (Theorem 1.1, the Library's
`RegularOrbitalFourierRegularityStatement`) and expands this integral by the Weyl integration
formula over the Cartan subalgebras. The dilation half of Lemma 3.16 is proved in the Library
(`RegularOrbitalVanishing.scalarDilation`, module
`Langlands.HarmonicAnalysis.UnitConjugation.OrbitalVanishingTransport`).

Kottwitz, *Harmonic analysis on reductive p-adic groups and Lie algebras*, in *Harmonic
Analysis, the Trace Formula, and Shimura Varieties*, Clay Math. Proc. 4, 2005, source ID
`arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura` (PDF page = printed page + 12),
proof of Theorem 27.5, printed pp. 516–517: "the Fourier transform also takes `C₁`
isomorphically onto itself", `C₁` being the space of test functions with vanishing regular
semisimple orbital integrals.
