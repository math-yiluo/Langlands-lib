# Row Fourier surjectivity for arbitrary p-adic Haar measure

Worker 457 authored these derived harmonic-analysis statement targets.
Both declarations are Prop-valued definitions. This module supplies no proof.

`Langlands.HarmonicAnalysis.PadicRowFourierSurjectivityStatement.{u} F T d`
has implicit prime parameter `p` with `[Fact p.Prime]`, and explicit parameters
`F : PadicField.{u} p`, `T : F.TopologicalData`, and `d : ℕ`. It installs
exactly `T.topology` on `F.Carrier` and that topology's Borel measurable space.
For every `ψ : UnitaryAdditiveCharacter F.Carrier`, every regular scalar
`ν : AdditiveHaarMeasure F.Carrier`, and every
`Φ : SchwartzBruhat (Fin d → F.Carrier)`, it asserts existence of
`κ : SchwartzBruhat (Fin d → F.Carrier)` with `IsRowFourierPair ψ ν κ Φ`.
Thus its pointwise conclusion is

```
Φ(y) = ∫ x, ψ.complex (∑ i, x i * y i) * κ(x) ∂rowMeasure ν d.
```

The pairing has a plus sign and no conjugation. The measure is the actual
finite product of the supplied scalar Haar measure, and both functions are
actual locally constant compactly supported complex functions. These are
imported unchanged from `HarmonicAnalysis.RowFourier` and `Basic`.
There is no chosen topology or preferred scalar measure, no self-duality
hypothesis on `ν`, and no positive-dimension restriction. For `d = 0` the
row space is a singleton and `rowMeasure ν 0` is unit point mass, as proved
in `RowFourier`; the target therefore includes this case without a
normalization factor depending on `ν`.

`Langlands.HarmonicAnalysis.RowFourierHaarSurjectivityStatement.{u}` is a
separate conditional target. Its explicit data are a field `K`, its supplied
topology and Borel measurable space, a character `ψ`, a regular scalar Haar
measure `μ`, and `d`. Its typeclass hypotheses require a topological ring,
local compactness, Hausdorffness, and second countability. Assuming both
`RowFourierClosed ψ μ d` and `IsRowSelfDual ψ μ d`, it asserts the same
surjectivity for every other scalar Haar measure `ν`. It does not assert
existence of `μ` with those two properties and does not replace the
unconditional p-adic target.

The Haar-uniqueness hypotheses are exposed in this helper: local compactness,
Hausdorffness, Borel measurability and regularity of both measures, the last
already part of `AdditiveHaarMeasure`. Second countability also ensures
sigma-finiteness of every scalar Haar measure and the usual finite-product
Borel structure needed by the intended integral proof. In the p-adic
specialization, the supplied `T.localField` gives local compactness and the
topological ring, `T.fieldT2` from `LocalField.Topology` gives Hausdorffness,
and `T.moduleTopology` identifies the finite-dimensional p-adic module
topology. A basis gives a homeomorphism with a finite power of `Padic p`,
hence second countability. These are proof obligations to discharge using
the supplied `T`, not extra assumptions on the main target.

The intended derived normalization argument is as follows. Haar uniqueness
for the regular scalar measures gives `ν = c • μ` with a positive finite
real scalar `c`, represented by a positive `NNReal`. Consequently

```
rowMeasure ν d = c^d • rowMeasure μ d,
FT[ψ,ν](f) = c^d * FT[ψ,μ](f).
```

Here the measure scalar is interpreted in `ℝ≥0∞` and the integral scalar
in `ℂ`. The already published `AdditiveHaarMeasure.scale` in
`CharacterTransport` and `rowCoordinateMeasure_scale` in `RowFourierMeasure`
expose the product law; a constant coordinate family has product `c^d`.
If `Φ⁻(x) = Φ(-x)`, closure for `μ` supplies the Schwartz--Bruhat function
`g = FT[ψ,μ](Φ⁻)`. Row self-duality then gives `FT[ψ,μ](g) = Φ`.
The required kernel for `ν` is `κ = (c^d)⁻¹ * g`. This explains both the
reflection sign and the inverse product factor. At dimension zero,
`c^0 = 1`. This paragraph describes a future proof route; this module
proves neither Haar uniqueness, integrability transport nor surjectivity.

The consumer is Fourier smearing in Jacquet, Piatetski-Shapiro and Shalika,
*Rankin--Selberg Convolutions* (1983), printed pp.394–395, and their
*Automorphic Forms on GL(3) I* (1979), Proposition 4.1.4 and Lemma 4.1.5,
printed pp.188–190. The latter proof on p.189 invokes Fourier inversion to
recover a cutoff from the weight `Φ̂(-z)`; the former uses its row-space
version. Those originals motivate this interface but do not state the
arbitrary-Haar target in this form. Their self-invariant normalization is
not imposed on the supplied `ν` here.

The analytic provenance is Weil, *Basic Number Theory*, second edition
(1973), Chapter VII §2, printed pp.104–108: p.105 explains linear scaling
of Fourier transforms, inverse scaling of dual measures, and self-dual
measure existence; Definition 1 on p.106 defines the test functions;
Proposition 2 on p.107 and Corollary 2 on p.108 give their Fourier
preservation and admissibility. The passage from scalar inversion to the
finite row product, the arbitrary-Haar factor `c^d`, and the two Lean targets
are derived formulations. A future proof may reuse the existing separate
row-compatibility proof task and a scalar self-dual-existence prerequisite;
neither pending statement is used as evidence of its conclusion here.

Registered originals read for this statement:

- `jpss-1983-rankin-selberg`, retained PDF
  `/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
  SHA256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`;
  printed pp.394–395 were inspected visually.
- `jps-1979-gl3-i`, retained PDF
  `/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Automorphic Forms on GL(3) I--1979.pdf`,
  SHA256 `6446822f267f9f95156ce7a193409209e56ce7858ed6d3d350480e73f35b1aa5`;
  printed pp.188–190 were read, with the Fourier formula on p.189 inspected visually.
- `weil-1973-basic-number-theory`, retained PDF
  `/home/taskhub/central-library/Weil--Basic number theory (book, 2nd edition)--1973.pdf`,
  SHA256 `32fff78f8ccc5d6378907941e26746c34e20fc3adf5096508844cfe8a301e33b`;
  Chapter VII §2, printed pp.104–108 were read.

The scalar-normalization warning in `LocalFactor/Harmonic/Statement.md`
was also checked against Tate (1979), §3.6, printed p.17. Its sentence after
(3.6.2) prints a negative exponent for the fixed-Haar to self-dual ratio;
this module uses no conductor-volume ratio from that sentence. Its only
normalization factor is the positive Haar scalar raised to the row dimension.
