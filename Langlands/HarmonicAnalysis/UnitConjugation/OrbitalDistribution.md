# Orbital distributions for the conjugation action of the units of an algebra

The module `Langlands.HarmonicAnalysis.UnitConjugation.OrbitalDistribution` defines the
centralizer of an element `X₀` of a ring `A` in the unit group `Aˣ`, the orbital integrand
`C g ↦ f(g⁻¹ X₀ g)` on the Library's left coset space `C \ Aˣ`, absolute convergence of the
orbital integrals for a measure `ν` on `C \ Aˣ`, and the orbital distribution
`f ↦ ∫_{C \ Aˣ} f(g⁻¹ X₀ g) dν(C g)`. It proves that the orbital distribution is supported in
the closure of the orbit, is conjugation-invariant when `ν` is right-invariant (in particular
when `ν` is a compatible quotient measure), and so lies in `J({X₀})`; it computes the orbit of
`0`.

## Setting

`A : Type v` a ring, regarded as the Lie algebra of `Aˣ` acting by conjugation (see
`Langlands.HarmonicAnalysis.UnitConjugation.InvariantDistribution`). The intended application
is Harish-Chandra's setting: a finite-dimensional semisimple algebra `A` over a nonarchimedean
local field `F` of characteristic zero, with its module topology. In characteristic zero such an
`A` stays semisimple after extension of scalars to an algebraic closure, and `Aˣ` is the group of
`F`-points of the connected reductive group `GL₁(A)`. Characteristic zero is needed here: over
`F = 𝔽₂((t))` the field `A = F(√t)` is semisimple, but `GL₁(A)` is not reductive. The coset
space is `QuotientIntegration.LeftQuotient C`, the space of cosets `C g` with the quotient
topology, and the measures are explicit arguments with explicit measurable structures, as in
`Langlands.Analysis.Local.QuotientMeasure`.

## Definitions

- `conjugationCentralizer X₀ : Subgroup Aˣ`: the stabilizer of `X₀` for Mathlib's conjugation
  action of `ConjAct Aˣ` on `A`, pulled back to `Aˣ` (`mem_conjugationCentralizer_iff_smul`);
  equivalently the units commuting with `X₀` (`mem_conjugationCentralizer_iff`). Every unit
  centralizes `0` (`conjugationCentralizer_zero`).
- `orbitalIntegrand X₀ f : LeftQuotient (conjugationCentralizer X₀) → ℂ`: the descent
  (`QuotientIntegration.descend`) of `g ↦ f(g⁻¹ X₀ g)`, which is constant on the cosets `C g`
  because `(h g)⁻¹ X₀ (h g) = g⁻¹ X₀ g` for `h ∈ C` (`orbitalIntegrand_mk`). It is additive and
  homogeneous in `f` (`orbitalIntegrand_add`, `orbitalIntegrand_smul`), and for `X₀ = 0` it is
  the constant `f(0)` (`orbitalIntegrand_zero`).
- `OrbitalIntegralConverges X₀ ν`: for every Schwartz–Bruhat function `f` on `A`, the orbital
  integrand of `f` is `ν`-integrable (`MeasureTheory.Integrable`: almost everywhere strongly
  measurable for `ν`, with finite integral of the complex norm), that is every test integral
  converges absolutely.
- `orbitalDistribution X₀ ν hν : Distribution A`, under `hν : OrbitalIntegralConverges X₀ ν`:
  `f ↦ ∫ q, orbitalIntegrand X₀ f q ∂ν` (`orbitalDistribution_apply`). Linearity uses the
  convergence premise.

## Properties

- `orbitalDistribution_mem_supportedOn`: the orbital distribution annihilates every test
  function vanishing on the closure of the orbit `conjugationSaturation {X₀}`, since
  `g⁻¹ X₀ g` is the conjugate of `X₀` by `g⁻¹`.
- `orbitalIntegrand_pullback_conjugation`: the orbital integrand of `f ∘ Ad u` is that of `f`
  composed with the right translation by `u⁻¹` on `C \ Aˣ`
  (`QuotientIntegration.rightTranslate`).
- `orbitalDistribution_isConjugationInvariant`: if every right translation preserves `ν`, the
  orbital distribution is conjugation-invariant (change of variables along the homeomorphism
  `rightTranslate C u⁻¹`).
- `orbitalDistribution_mem_invariantSupportedIn`: under the same hypothesis the orbital
  distribution lies in `invariantSupportedIn {X₀}`, Harish-Chandra's `J({X₀})`;
  `orbitalDistribution_mem_invariantSupportedIn_of_isCompatible` takes the right invariance from
  `QuotientIntegration.IsCompatible C μG μH ν` (its field `right_invariant`), for measures `μG`
  on `Aˣ` and `μH` on `C` with `μH` right-invariant.
- The orbit of `0`: `orbitalIntegralConverges_zero` (a finite `ν` gives convergence) and
  `orbitalDistribution_zero_apply`: under the convergence premise, the orbital distribution of
  `0` is `f ↦ ν.real Set.univ · f(0)`, a multiple of the Dirac distribution at `0` (for
  `X₀ = 0` the coset space has one point). Here `ν.real Set.univ` is
  `(ν Set.univ).toReal`, which is `0` for an infinite total mass; for a finite `ν` it is the
  total mass of `ν`.
- Nilpotent orbits: `isNilpotent_of_mem_conjugationSaturation`: the conjugates of a nilpotent
  element are nilpotent, so the orbit of a nilpotent `N` consists of nilpotent elements.

## Sources and conventions

Harish-Chandra, *Admissible invariant distributions on reductive p-adic groups*, with notes by
S. DeBacker and P. J. Sally, Jr., University Lecture Series 16, AMS, 1999, source ID
`harish-chandra-1999-admissible-invariant-distributions` (PDF page = printed page + 15),
Introduction, printed pp. 2–3 (PDF pp. 17–18): for an orbit `O` and `X₀ ∈ O`, `C_G(X₀)` is
unimodular, `G/C_G(X₀)` carries an invariant measure `dx*` unique up to a constant factor, and
by a theorem of Deligne and Ranga Rao `μ_O(f) = ∫_{G/C_G(X₀)} f(x.X₀) dx*` is well defined for
`f ∈ C_c^∞(g)`; nilpotent orbits are the orbits of nilpotent elements, and `{0}` is a nilpotent
orbit (printed p. 3).

Conventions here:

- The quotient is the Library's left coset space `C \ Aˣ` with `g ↦ g⁻¹ X₀ g`. The map
  `C g ↦ g⁻¹ C` is a homeomorphism `C \ Aˣ → Aˣ/C` carrying `C g ↦ f(g⁻¹ X₀ g)` to
  `x C ↦ f(x X₀ x⁻¹) = f(x.X₀)`, and right-invariant measures on `C \ Aˣ` to left-invariant
  measures on `Aˣ/C`.
- The measure `ν` is an explicit argument, and the construction accepts every measure for which
  the convergence premise holds; for instance `ν = 0` gives the zero functional. Harish-Chandra's
  orbital distributions arise from the quotient measures compatible with Haar measures `μG` on
  `Aˣ` and `μH` on `C` (`QuotientIntegration.IsCompatible`: nonzero, regular, right-invariant,
  with the Weil integral formula). In the characteristic-zero setting above, inversion carries
  such a `ν` to a nonzero regular invariant measure on `Aˣ/C`, an instance of the measure `dx*`
  of the source formula, so that `orbitalDistribution X₀ ν hν` is Harish-Chandra's `μ_O` for that
  choice of `dx*`. The positive constant up to which `dx*` is determined corresponds to the
  choice of the invariant quotient measure; for a compatible `ν` it is fixed by `μG` and `μH`
  through the Weil formula.
- Convergence is an explicit premise (`OrbitalIntegralConverges`): this module does not prove
  the Deligne–Ranga Rao convergence theorem, and defines the orbital distribution under the
  premise.

## Scope

The centralizer and the descent of the integrand (`conjugationCentralizer`, `orbitalIntegrand`)
use only the ring structure. `OrbitalIntegralConverges` and `orbitalDistribution` also use a
topology on `A`, through the Schwartz–Bruhat space `SchwartzBruhat A`, and a measurable structure
on the coset space. The conjugation results use that `A` is a topological ring (so that `Aˣ` is a
topological group and conjugation is a homeomorphism);
`orbitalDistribution_isConjugationInvariant` and `orbitalDistribution_mem_invariantSupportedIn`
also assume that the coset space carries its Borel σ-algebra, and
`orbitalDistribution_mem_invariantSupportedIn_of_isCompatible` assumes the same of `Aˣ`.
Neither the existence of compatible quotient measures, nor the unimodularity of centralizers,
nor the convergence of orbital integrals is proved here.
