# Harish-Chandra's space `D₀`, nilpotent orbital distributions and dilations

The module `Langlands.HarmonicAnalysis.UnitConjugation.RegularOrbitalVanishing` names the
objects that Harish-Chandra's proof of Theorem 3.1 manipulates, for the Lie algebra `A` of the
unit group `Aˣ` of a finite-dimensional algebra over a field `F`
(`Langlands.HarmonicAnalysis.LieAlgebraRegularOrbitalDensityStatement`, module
`Langlands.HarmonicAnalysis.UnitConjugation.RegularOrbitalDensityStatement`).

## Definitions

All in the namespace `Langlands.HarmonicAnalysis.UnitConjugation`.

- `RegularOrbitalVanishing F A f`: for every regular `X ∈ regularSet F A`, every Borel
  σ-algebra on the coset space `LeftQuotient (conjugationCentralizer X)`, every Haar measure
  `μG` on `Aˣ`, every right-invariant Haar measure `μH` on the centralizer `C` of `X`, every
  quotient measure `ν` with `IsCompatible C μG μH ν` and every proof `hconv` of absolute
  convergence, `orbitalDistribution X ν hconv f = ∫_{C \ Aˣ} f(g⁻¹ X g) dν = 0`. This is
  word for word the hypothesis on `f` in `LieAlgebraRegularOrbitalDensityStatement`, that is
  Harish-Chandra's condition `f ∈ D₀` (the Markdown page of
  `Langlands.HarmonicAnalysis.UnitConjugation.RegularOrbitalDensityStatement` explains why the
  vanishing of the orbital integrals over all regular orbits is the vanishing of the functions
  `φ_f^h` for all Cartan subalgebras `h`).
- `nilpotentOrbitals A`: the set of distributions `orbitalDistribution N ν hconv` for nilpotent
  `N : A` and, as above, any Borel σ-algebra on the coset space of the centralizer of `N`, any
  Haar measure on `Aˣ`, any right-invariant Haar measure on the centralizer, any compatible
  quotient measure `ν` and any convergence proof: the nilpotent orbital integrals `μ_O`, each
  up to the positive factor fixing the invariant measure.
- `scalarDilation s f`, for a unit `s` of the field: the test function `X ↦ f(s⁻¹ X)`
  (`scalarDilation_apply`), the pullback along the homeomorphism `X ↦ s⁻¹ • X`.
- `RegularOrbitalDensityFor F A`: Theorem 3.1 for the single algebra `A`: for every module
  topology on `A` and Borel σ-algebra on `Aˣ`, with the topological ring structure
  `IsModuleTopology.isTopologicalRing F A`, every conjugation-invariant distribution `T`
  satisfies `T f = 0` for every `f` with `RegularOrbitalVanishing F A f`.

`lieAlgebraRegularOrbitalDensityStatement_iff` (proved by `Iff.rfl`) states that
`LieAlgebraRegularOrbitalDensityStatement` is `RegularOrbitalDensityFor F A` for every
nonarchimedean local field `F` of characteristic zero and every finite-dimensional semisimple
`F`-algebra `A`.

## Source

Harish-Chandra, *Admissible invariant distributions on reductive p-adic groups*, with notes by
S. DeBacker and P. J. Sally, Jr., University Lecture Series 16, AMS, 1999, source ID
`harish-chandra-1999-admissible-invariant-distributions` (PDF page = printed page + 15):
§3, printed p. 17 (PDF p. 32): "Let `D₀` be the space of all `f ∈ D` such that `φ_f^h = 0`
for all Cartan subalgebras `h` of `g`"; §3.1, printed p. 17: "For `f ∈ D`, `X ∈ g`, and
`t ∈ Ω^×` define `f_t(X) = f(t⁻¹X)`", and, for a nilpotent orbit `O ∋ X₀`,
`μ_O(f) = ∫_{G/C_G(X₀)} f(x.X₀) dx*`, defined by the theorem of Deligne and Ranga Rao.
