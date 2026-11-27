# Invariant distributions are determined by regular orbital integrals

The module `Langlands.HarmonicAnalysis.UnitConjugation.RegularOrbitalDensityStatement` states, as
the proposition `Langlands.HarmonicAnalysis.LieAlgebraRegularOrbitalDensityStatement.{u, v}`,
Harish-Chandra's Theorem 3.1 for the Lie algebra `A` of the unit group `Aˣ` of a
finite-dimensional semisimple algebra over a nonarchimedean local field of characteristic zero:
a Schwartz–Bruhat function all of whose regular orbital integrals vanish is annihilated by every
conjugation-invariant distribution. The statement is **not** proved here.

## Statement

`LieAlgebraRegularOrbitalDensityStatement.{u, v}` quantifies over

- a field `F : Type u` with `[ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [CharZero F]`: a nonarchimedean local field of characteristic
  zero;
- `A : Type v` with `[Ring A] [Algebra F A] [FiniteDimensional F A] [IsSemisimpleRing A]
  [TopologicalSpace A] [IsModuleTopology F A]`: a finite-dimensional semisimple `F`-algebra with
  its module topology, and a Borel σ-algebra on `Aˣ` (`[MeasurableSpace Aˣ] [BorelSpace Aˣ]`,
  for the topology of `Aˣ` as the units of the topological ring `A`); the topological ring
  structure is `IsModuleTopology.isTopologicalRing`, bound with `haveI` inside the statement;
- a Schwartz–Bruhat function `f : SchwartzBruhat A`.

The hypothesis: for every regular `X ∈ regularSet F A` (Harish-Chandra's `g'`, defined in
`Langlands.HarmonicAnalysis.UnitConjugation.RegularSet` by `η(X) ≠ 0`), every Borel σ-algebra
on the coset space `LeftQuotient (conjugationCentralizer X)` of the centralizer
`C = conjugationCentralizer X`, every Haar measure `μG` on `Aˣ`, every Haar measure `μH` on `C`
that is also right-invariant, every quotient measure `ν` on `C \ Aˣ` with
`QuotientIntegration.IsCompatible C μG μH ν`, and every proof `hconv` of absolute convergence
of the orbital integrals (`OrbitalIntegralConverges X ν`),

`orbitalDistribution X ν hconv f = ∫_{C \ Aˣ} f(g⁻¹ X g) dν(C g) = 0`.

The claim: `T f = 0` for every distribution `T` on `A` invariant under conjugation by `Aˣ`
(`IsConjugationInvariant T`).

## Source

Harish-Chandra, *Admissible invariant distributions on reductive p-adic groups*, with notes by
S. DeBacker and P. J. Sally, Jr., University Lecture Series 16, AMS, 1999, source ID
`harish-chandra-1999-admissible-invariant-distributions` (PDF page = printed page + 15):

- Introduction, printed pp. 1–3 (PDF pp. 16–18): `J`, the space of `G`-invariant distributions
  on `g`; `η` and `g'`; the invariant measure `dx*` on `G/C_G(X₀)` and the orbital integral
  `μ_O(f) = ∫_{G/C_G(X₀)} f(x.X₀) dx*`.
- §1, printed p. 5 (PDF p. 20): for a Cartan subalgebra `h`, with `A` the split component of the
  corresponding Cartan subgroup, `φ_f(H) = |η(H)|^{1/2} ∫_{G/A} f(x.H) dx*` for `H ∈ h' = h ∩ g'`.
- §3, printed p. 17 (PDF p. 32): "Let `D₀` be the space of all `f ∈ D` such that `φ_f^h = 0` for
  all Cartan subalgebras `h` of `g`." Theorem 3.1 (Theorem 10): "We have `T(f) = 0` for `T ∈ J`
  and `f ∈ D₀`." The proof occupies §3, printed pp. 17–30.

Correspondence with the statement:

- `G = Aˣ`, the `F`-points of the connected reductive group `GL₁(A)`, acting on its Lie
  algebra `A` by conjugation; `J` is the space of distributions `T` with
  `IsConjugationInvariant T`.
- Every `X ∈ g'` lies in exactly one Cartan subalgebra, its centralizer `h` in `g`, and
  `X ∈ h'`; the centralizer `C` of `X` in `Aˣ` is the Cartan subgroup of `h`, and its split
  component `A_h` has compact quotient `C/A_h`. Hence
  `φ_f^h(X) = |η(X)|^{1/2} vol(C/A_h) μ_X(f)` with `|η(X)| ≠ 0`, where `μ_X` is the orbital
  integral for the invariant measure on `G/C`, and `f ∈ D₀` exactly when `μ_X(f) = 0` for every
  `X ∈ g'`.
- The Library's orbital distribution (`Langlands.HarmonicAnalysis.UnitConjugation.OrbitalDistribution`)
  integrates `g ↦ f(g⁻¹ X g)` over the left coset space `C \ Aˣ`; the map `C g ↦ g⁻¹ C`
  carries it to Harish-Chandra's `∫_{G/C} f(x.X) dx*`. A compatible quotient measure `ν` is an
  invariant measure on the coset space, unique up to a positive factor; the factor does not
  affect the vanishing of `μ_X(f)`.
- For `X ∈ g'` such data exist: `C` is abelian, hence unimodular, so a compatible quotient
  measure exists, and the orbital integrals of `X` converge (Introduction, printed pp. 2–3, by
  the theorem of Deligne and Ranga Rao). So the hypothesis of the statement is exactly
  `f ∈ D₀`, and the statement is Theorem 3.1.

Harish-Chandra derives Lemma 4.1 from Theorem 3.1 (§4, printed p. 30, PDF p. 45): for a
`G`-domain `V` and a test function `f` whose orbital integrals over the regular orbits in `V`
vanish, the product of `f` with the characteristic function of `V` lies in `D₀`, so every
distribution in `J(V)` vanishes at `f`. Lemma 4.1 enters the proofs of Corollary 4.2 and of
Theorem 4.4 (1).
