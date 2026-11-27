# Harish-Chandra's Theorem 4.4 (1) from its four inputs

The module `Langlands.HarmonicAnalysis.UnitConjugation.FourierRegularityReduction` carries out
Harish-Chandra's derivation of the local summability clause of Theorem 4.4 for the Lie algebra
`A` of the unit group of a finite-dimensional semisimple algebra over a nonarchimedean local
field of characteristic zero. It states, as
`Langlands.HarmonicAnalysis.LieAlgebraFourierRegularityReductionStatement.{u', v'}`, the
implication

`LieAlgebraHoweFinitenessStatement → LieAlgebraRegularOrbitalDensityStatement →
  LieAlgebraConjugationDomainStatement → RegularOrbitalFourierRegularityStatement →
  LieAlgebraFourierRegularityStatement`

(all at the universes `{u', v'}` of `F` and `A`), and proves it:
`Langlands.HarmonicAnalysis.lieAlgebraFourierRegularityReduction`. The four premises are
Howe's finiteness theorem (Harish-Chandra's Theorem 12.1), Theorem 3.1, Lemma 4.3 and the local
summability in Theorem 1.1; the module does not prove them.

## Source

Harish-Chandra, *Admissible invariant distributions on reductive p-adic groups*, with notes by
S. DeBacker and P. J. Sally, Jr., University Lecture Series 16, AMS, 1999, source ID
`harish-chandra-1999-admissible-invariant-distributions` (PDF page = printed page + 15), §4,
printed pp. 30–31 (PDF pp. 45–46): Lemma 4.1, Corollary 4.2, Lemma 4.3 and the proof of
Theorem 4.4 (Theorem 3), which "does not prove (3)" and proves clause (1) with the local
summability. The implementation follows that proof; the steps below name the source step each
one implements.

## Helper declarations

In the namespace `Langlands.HarmonicAnalysis.FourierRegularityReduction`:

- `restrictToLatticeTests_apply`: the restriction `restrictToLatticeTests L T`
  (`Langlands.HarmonicAnalysis.UnitConjugation.HoweRestriction`, Harish-Chandra's `j_L T`)
  evaluates `T` at an `L`-invariant test function in `latticeInvariantTests L`
  (`Langlands.HarmonicAnalysis.UnitConjugation.LatticeTests`).
- `Langlands.Whittaker.BruhatCompatibleSupport.clopenCutoff hD f`: the product of a test function `f` with the characteristic function of a
  clopen set `D` (`clopenCutoff_apply_of_mem`, `clopenCutoff_apply_of_notMem`).
- `regularOrbitals F D`: the orbital distributions `orbitalDistribution X ν hconv` of the
  regular elements `X ∈ regularSet F A` lying in `D`, for every Borel σ-algebra on the coset
  space, every Haar measure `μG` on `Aˣ`, every right-invariant Haar measure `μH` on the
  centralizer, every compatible quotient measure `ν` and every convergence proof `hconv`.
- `conjugationSaturation_subset_of_invariant`, `conjugationSaturation_singleton_subset`,
  `mem_invariantSupportedIn_of_mem_saturation`: the saturation of a subset of an invariant set
  lies in it; the orbit of a point of `ω₀^G` lies in `ω₀^G`, so `J({X}) ⊆ J(ω₀)` for
  `X ∈ ω₀^G`.

## Proof

Let `T ∈ J(ω)` with `ω` compact.

1. **Lemma 4.3** (`LieAlgebraConjugationDomainStatement`) gives a compact `ω₀` and a clopen
   conjugation-invariant `D` with `ω ⊆ D ⊆ ω₀^G`.

2. **Lemma 4.1.** `apply_clopenCutoff`: since `D` is closed, invariant and contains `ω`, it
   contains the closure of `ω^G`, the support of `T`, so `T` does not change when a test function
   `g` is replaced by `clopenCutoff hD g`, because their difference vanishes on `D`.
   `orbitalDistribution_clopenCutoff_of_mem` and `orbitalDistribution_clopenCutoff_of_notMem`:
   for `X ∈ D` the whole orbit of `X` lies in `D` and the orbital integral of the cutoff equals
   that of `g`; for `X ∉ D` the orbit misses `D` and the orbital integral of the cutoff is `0`.
   Hence if the orbital integrals of `g` vanish for the regular elements of `D`, those of the
   cutoff vanish for all regular elements, and Theorem 3.1
   (`LieAlgebraRegularOrbitalDensityStatement`, applied to the invariant distribution `T`)
   gives `T g = T (clopenCutoff hD g) = 0`.

3. **Corollary 4.2** (`exists_mem_span_regularOrbitals_eq`). Let `L` be an open subgroup,
   `j_L = restrictToLatticeTests L`, and `S` the image under `j_L` of the span of
   `regularOrbitals F D`. Every generator `μ_X` (with `X ∈ D ⊆ ω₀^G`) lies in
   `J({X}) ⊆ J(ω₀)` (`orbitalDistribution_mem_invariantSupportedIn_of_isCompatible`), so `S` is
   contained in `j_L J(ω₀)`, which is finite-dimensional by Howe's theorem
   (`LieAlgebraHoweFinitenessStatement` for `ω₀` and `L`); `S` is finite-dimensional. For a
   finite-dimensional subspace `S` of the dual of `latticeInvariantTests L`, Mathlib's
   `Subspace.dualCoannihilator_dualAnnihilator_eq` says that `S` is the annihilator of its
   annihilator in `latticeInvariantTests L`. If `j_L T ∉ S`, there is therefore an
   `L`-invariant test function `g` killed by every element of `S`, in particular by every `μ_X`
   with `X ∈ D` regular, with `T g ≠ 0`; this contradicts step 2. So `j_L T ∈ S`: there is
   `R ∈ span (regularOrbitals F D)` with `T g = R g` for every `g ∈ latticeInvariantTests L`.

4. **Theorem 1.1** (`exists_density_of_mem_span`). By induction over the span
   (`Submodule.span_induction`), the Fourier transform of every `R ∈ span (regularOrbitals F D)`
   is given by a locally integrable function: `RegularOrbitalFourierRegularityStatement` for the
   generators, `0` for `0`, and sums and scalar multiples of densities for linear combinations.
   The integrals add because `Θ f` is integrable for `Θ` locally integrable and `f` continuous
   with compact support (`LocallyIntegrable.integrable_smul_right_of_hasCompactSupport`).

5. **Theorem 4.4 (1)** (`lieAlgebraFourierRegularityReduction`). Fix `x ∈ A`. The algebra `A`
   has compact open subgroups containing any compact set
   (`compactOpenExhaustion_of_finiteDimensional`); take one, `M`, containing `x`, and let `L` be
   the annihilator of `M` for the self-dual bicharacter `(Y, Z) ↦ ψ(B(Y, Z))`
   (`isSelfDualBicharacter_pairingCharacter`), an open subgroup because `M` is compact
   (`IsSelfDualBicharacter.isOpen_annihilator`). For a test function `f` supported in `M`, `f̂`
   is `L`-invariant (`bicharacterFourierSB_annihilatorInvariant`), so by steps 3 and 4

   `T̂(f) = T(f̂) = R(f̂) = R̂(f) = ∫ θ f dμ`

   with `θ` locally integrable: `T̂` has a locally integrable density on the open neighbourhood
   `M` of `x`. The Library's gluing theorem
   `Distribution.exists_locallyIntegrableDensity_of_locally` (for the single distribution `T̂`,
   the measure `μ` and no prescribed points of local constancy) combines these local densities
   into one locally integrable `Θ` with `T̂(f) = ∫ Θ f dμ` for every `f`. Its hypotheses on `A`
   (Hausdorff, locally compact, second countable, totally disconnected) come from the
   finite-dimensional module topology (`t2Space_of_finiteDimensional`,
   `locallyCompactSpace_of_finiteDimensional`, `secondCountableTopology_of_finiteDimensional`),
   total disconnectedness from Mathlib's `NonarchimedeanAddGroup` instance, the compact open
   subgroups forming a basis of neighbourhoods of `0`.

The Borel σ-algebra `borel Aˣ` on the unit group is used to instantiate the premises that
quantify over one; the conclusion does not involve it.
