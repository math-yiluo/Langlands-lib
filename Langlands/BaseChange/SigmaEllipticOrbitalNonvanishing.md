# Nonvanishing of σ-orbital integrals on an open set of σ-elliptic elements

The module `Langlands.BaseChange.SigmaEllipticOrbitalNonvanishing` proves that a test function
`φ` on `GL_n(E)` whose σ-orbital integrals vanish off the σ-elliptic set, and whose integral
against a σ-conjugation invariant function `Θ` is nonzero, has σ-orbital integrals that do not
vanish on a nonempty open set of σ-elliptic elements. With `Θ` the twisted character function
of an irreducible representation `(τ, A)` and `φ` a twisted pseudo-coefficient of it, this is
clause (d) of `TwistedCuspidalPseudoCoefficientExistenceStatement` (Henniart–Lemaire 2011,
II.5.14, Corollaire 2; Arthur–Clozel 1989, Chapter 1, Lemma 2.12). The proof does not use the
twisted Weyl integration formula.

## Main theorem

`exists_isOpen_sigmaElliptic_sigmaOrbitalIntegral_ne_zero`. Let `F` be a nonarchimedean local
field of characteristic zero, `E` a commutative `F`-algebra with its module topology that is
cyclic of group `⟨σ⟩` of order `l` (`IsCyclicAlgebra σ l`), and give `GL_n(E)` a σ-algebra for
which it is a Borel space. Let `μ` be a Haar measure on `GL_n(E)`, `φ` a Schwartz–Bruhat function
and `Θ : GL_n(E) → ℂ` such that

- `g ↦ φ(g) Θ(g)` is `μ`-integrable and `∫ φ Θ dμ ≠ 0`;
- `Θ(x⁻¹ δ x^σ) = Θ(δ)` for every σ-regular `δ` and every `x`;
- the σ-orbital integrals of `φ` vanish at every σ-regular element that is not σ-elliptic
  (`SigmaOrbitalIntegralsVanishOffElliptic σ l μ ⇑φ`).

Then there is a nonempty open set `V ⊆ GL_n(E)` of σ-elliptic elements such that for every
`δ ∈ V`, every right Haar measure `μδ` on the σ-centralizer `sigmaCentralizer σ n δ` and every
quotient measure `νδ` compatible with `μ` and `μδ` (`IsCompatible`),
`sigmaOrbitalIntegral σ n δ νδ φ ≠ 0`. The conclusion is clause (d) of
`TwistedCuspidalPseudoCoefficientExistenceStatement` verbatim.

### Proof

1. **A nonzero σ-orbital integral.** At a σ-regular `δ`, invariance of `Θ` gives
   `Λ_σ(φ Θ, δ) = Θ(δ) Λ_σ(φ, δ)` for every quotient measure. If every σ-orbital integral of `φ`
   at σ-regular elements vanished, so would those of `φ Θ`, and
   `integral_eq_zero_of_sigmaOrbitalIntegral_eq_zero` (module
   `Langlands.BaseChange.SigmaDiscreteEllipticNonvanishingReduction`) would give `∫ φ Θ dμ = 0`.
   So some σ-regular `δ₀`, with some compatible pair of measures, has a nonzero σ-orbital
   integral; by the third hypothesis `δ₀` is σ-elliptic.
2. **Local constancy.** `regularOrbitalProfileExistence` (module
   `Langlands.BaseChange.RegularOrbitalProfileExistence`) gives, on the open set `R` of σ-regular
   elements, a choice of compatible measures `mE` at every point and regular orbital profile data
   `dE`: in particular the normalized σ-orbital integrals `r ↦ Λ_σ(f, r; mE)` are locally
   constant on `R` for every test function `f` supported in `R`. The auxiliary theorem
   `RegularOrbitalProfileData.isLocallyConstant_twistedOrbitalIntegral` removes the support
   condition (below), so `r ↦ Λ_σ(φ, r; mE)` is locally constant on `R`: it is constant on an
   open neighbourhood `U` of `δ₀` in `R`.
3. **Change of measures.** At each σ-regular `s`, any compatible pair `(μδ, νδ)` gives
   `Λ_σ(φ, s; νδ) = c · Λ_σ(φ, s; mE)` with `c > 0`
   (`exists_twistedOrbitalIntegral_eq_smul_of_isCompatible`). Applied at `δ₀` this shows
   `Λ_σ(φ, δ₀; mE) ≠ 0`; then on `U` the normalized integral is that nonzero value, and every
   compatible choice rescales it by a positive scalar.
4. `V` is the image of `U` in `GL_n(E)` intersected with the σ-elliptic set. It is open since
   `R` is open and the σ-elliptic set is open (`isOpen_setOf_isSigmaElliptic`, module
   `Langlands.BaseChange.EllipticLocusClopen`), and it contains `δ₀`.

## Auxiliary results

- `exists_twistedOrbitalIntegral_eq_smul_of_isCompatible`: for a continuous twist `θ` of a
  second countable locally compact Hausdorff group `G` and `δ ∈ G`, two pairs of a right Haar
  measure on the twisted centralizer of `δ` and a compatible quotient measure give twisted
  orbital integrals that differ by one positive scalar `c`, the same for every function. The
  twisted centralizer is closed (`isClosed_twistedCentralizer`), hence locally compact and second
  countable; its two Haar measures differ by `c = haarScalarFactor`, and
  `IsCompatible.eq_smul_of_subgroup_smul` with `twistedOrbitalIntegral_smul_measure` (module
  `Langlands.BaseChange.RegularTransferMeasures`) transfer the scalar to the quotient measures
  and the integrals.
- `RegularOrbitalProfileData.isLocallyConstant_twistedOrbitalIntegral`: for regular orbital
  profile data on an open set `R` of a locally profinite group and a continuous map `a` to a
  Hausdorff space that is constant on twisted conjugacy classes and whose fibres through `R` are
  single twisted conjugacy classes, the normalized twisted orbital integrals of every test
  function `f` are locally constant on `R`. Around `r ∈ R`, take a compact open `K ∋ r` inside
  `R`; the set `C = a⁻¹(a(K))` is closed (image of a compact set), equal to the union of the
  twisted conjugates of `K`, hence open, invariant and contained in `R`. The cut-off `1_C f` is a
  test function supported in `R` with the same twisted orbital integrals as `f` at the points of
  `C`, and the profile data give local constancy for it. The module
  `Langlands.BaseChange.ConcordanceLocallyConstantOfProfiles` contains the same argument as a
  private lemma; this is a public version.
- `exists_conj_of_coefficients_eq_of_isRegularSemisimple` and
  `exists_twistedConj_of_cyclicNorm_coefficients_eq`: two elements of `GL_n(F)`, the first
  regular semisimple, with equal characteristic polynomials are conjugate
  (`exists_matrix_conj_of_charpoly_eq_of_separable`); two elements of `GL_n(E)`, the first
  σ-regular, whose cyclic norms have equal characteristic polynomial coefficients are
  σ-conjugate (the norm lemma `cyclicNormLemma`, module `Langlands.BaseChange.CyclicNormLemma`,
  and `charpoly_eq_of_baseChange_coefficients`). These are public versions of private lemmas of
  `Langlands.BaseChange.ConcordanceLocallyConstantOfProfiles`. In step 2 they supply the fibre
  condition for `a = coefficients ∘ cyclicNorm σ l`, which is constant on σ-conjugacy classes by
  `coefficients_cyclicNorm_conj`.

## Sources

- G. Henniart and B. Lemaire, *Changement de base et induction automorphe pour `GL_n` en
  caractéristique non nulle*, Mém. SMF 124 (2011), II.5.14, Corollaire 2 and its proof
  (printed p. 117): if all σ-orbital integrals of a pseudo-coefficient vanished, its twisted
  traces would vanish by the integration formula (1) of II.2.10, contradicting trace `1`.
- J. Arthur and L. Clozel, *Simple Algebras, Base Change, and the Advanced Theory of the Trace
  Formula*, Annals of Math. Studies 120 (1989), Chapter 1, Lemma 2.12 and its proof (printed
  p. 19).
