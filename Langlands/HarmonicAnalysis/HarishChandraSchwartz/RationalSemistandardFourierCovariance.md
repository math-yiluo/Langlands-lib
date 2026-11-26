# VII.1.4: Weyl covariance of the actual full Fourier family

This module states Waldspurger's Lemma VII.1.4 for the full Fourier family
`rationalSemistandardFourierFamily` of `RationalSemistandardFourierFamily`.
The comparison is the actual normalized V.3 comparison carried by
`RationalSemistandard.WeylSectionComparisonData`. The module also states the
V.3.1 properties of that comparison in the fibers of the Fourier family. It
proves that these V.3.1 properties imply VII.1.4, following Waldspurger's proof.
It proves that VII.1.4 is the pointwise invariance relation `IsWeylInvariant` of
`RationalSemistandardInvariance`, imposed on the family of every Schwartz function.
Neither covariance nor the V.3.1 transport is proved here; both are named
Prop-valued targets.

Unqualified names are in `Langlands.HarishChandraSchwartz` or in
`Langlands.HarishChandraSchwartz.RationalSemistandard`, which the module opens.
`ActualConjugateLeviCoherence` abbreviates
`Langlands.Plancherel.ActualConjugateLeviCoherence`.

## Original source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d'après Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003), 235–333, registered
as `waldspurger-2003-plancherel` (printed page = PDF page + 234).

- **Lemma VII.1.4** (printed p. 317, PDF p. 83). For every `f ∈ C(G)`, every
  `s ∈ W^G`, every `P' ∈ P(s·M)` and every `ω ∈ O`,
  `ψ_f[sO, P']_{sω} = °c_{P'|P}(s, ω) ψ_f[O, P]_ω`. The proof pairs both sides
  with `°c_{P'|P}(s, ω) ψ` and applies Lemma VII.1.1(ii) and Lemma V.3.1 twice.
- **Lemma VII.1.1(ii)** (printed p. 314, PDF p. 80):
  `(E_P^G ψ, f)_G = (ψ, f̂(ω, P))`.
- **Lemma V.3.1** (printed p. 295, PDF p. 61). The normalized comparison
  `°c_{P'|P}(s, ω)` is unitary and satisfies `E_{P'}^G(°c_{P'|P}(s, ω) ψ) = E_P^G ψ`.
- **I.1** (printed pp. 238–240). Haar measures are normalized by giving the
  compact trace mass one. Formal degrees are taken for these measures.

## Hypotheses and data

The ambient data are those of `RationalSemistandardFourierFamily`. The field
is an arbitrary nonarchimedean local field, so positive characteristic is
allowed. The group is an affine, locally finite type, connected reductive
group scheme, with no split or quasisplit assumption. Rank zero is allowed,
and the field and representation-carrier universes are independent. The
remaining data are as follows.

- Compact data `d p`, modular comparison `hdelta p` and the ambient
  `SquareIntegrableWeight` `hsw`.
- Split components `a p` with quotient Haar measures `muM p`. These measures are
  Borel and inversion invariant.
- `hT`: tempered coefficient growth of the actual normalized induction of every
  discrete series modulo the split center.
- A comparison `C : WeylSectionComparisonData a ha muM d hG` for the same split
  components, measures and compact data. `C` contains the closed V.3
  existence and uniqueness statement `WeylSections.ClosedSectionComparisonStatement`
  at every compact lift. It also contains the cocharacter presentations, the
  common source compact and the intrinsic source normalization of its own Haar
  data. `C.fiberComparison t q n A` is defined at **every** actual inducing object
  `A` of the unitary orbit, not only at generic points.

### Measure normalization

Each target is an implication whose hypothesis, stated after all the parameters
above, is `SourceMeasure.IntrinsicQuotientNormalization a muM d`. This hypothesis
says the following for every index `p`. The trace of `(d p).compact` on the literal
Levi has an image in the quotient `levi p ⧸ (chosenLeviModel p).splitCenter (a p)`.
The measure `muM p` gives that image mass one (`IsNormalizedQuotientHaar`). This is
the I.1 convention. Under it, `SourceMeasure.weylQuotientHaar_map` gives

`Measure.map (SourceMeasure.weylQuotientHomeomorph C t q n) (muM q) = muM t.1`.

Here `SourceMeasure.weylQuotientHomeomorph C t q n` is the isomorphism from the
quotient at `q` to the quotient at `t.1`. It is induced by the inverse Levi
conjugation of the lift `n`. Inverse conjugation therefore pushes the target
measure `muM q` to the source measure `muM t.1`. Equivalently, conjugation pushes
the source measure to the target measure.

Covariance needs this compatibility of the two scales, not a particular absolute
scale. A formal degree scales inversely with the quotient Haar measure, and the
Fourier tensor contains the factor `d(ω)`. Rescaling `muM q` alone by `c > 0`
multiplies every Fourier tensor at the index `q` by `c⁻¹`. The tensors at `t.1` do
not change, so VII.1.4 can fail without a compatibility premise. Rescaling all the
quotient measures by the same `c` multiplies both sides of VII.1.4 by `c⁻¹`.

### The other data used by the targets

The covariance target evaluates the family `fam`. This family is built from
`hsw`, `hT`, `d` and `hdelta`, so the covariance target uses all of them. These
analytic inputs of the Fourier family are parameters of the target; the target does
not discharge them. Both targets use `d`, `hdelta` and `C`. Through the actual
common-Levi comparison, the certificate in `C` gives the regular extension of the
normalized V.3 comparison to every unitary point.

The equalities are asserted at every unitary point of every full index, on the
full dependent product. Neither target takes a smoothness witness or a
finite-support witness for the Fourier family. Neither assumes that tempered
parabolic induction is irreducible.

## The covariance target

`RationalSemistandardFourierCovarianceStatement hi hnu hKc hPK rho hsw a ha muM d hdelta hT C`
asserts the following under `IntrinsicQuotientNormalization a muM d`. Take any
Schwartz function `f`, any full index `t = (P, O)` and any `w : relativeWeylGroup i`.
Take any semistandard index `q` with
`relativeWeylConjugateSubgroupFunctor i t.1.levi _ w = q.levi`, that is,
`P' = q ∈ P(w·M)`. Take any compact lift `n : C.Lift t q` with
`(weylElement _ _ n).val = w`, and any actual inducing object `A` of `O`. Then

`fam f (C.target t q n) (C.representative t q n A) = C.fiberComparison t q n A (fam f t A)`.

Here `fam` is `rationalSemistandardFourierFamily hG hi hnu hKc hPK rho hsw a ha muM d hdelta hT`.
`C.target t q n` is the intrinsic full index `(q, sO)`, and
`WeylSectionComparisonData.target_transports` identifies `sO` as the orbit
transported by `w`. `C.representative t q n A` is the conjugate object `sω`,
reindexed in the chosen target orbit without changing the object. The equality
holds in the coefficient fiber of that conjugate object. This is the fiber in
which `C.fiberComparison t q n A` takes its values, so no further identification
of fibers is used. The statement quantifies over all lifts of `w`. The Library's
`WeylSectionComparisonData.exists_lift` shows that such a lift exists for every
`w` and every such `q`.

`rationalSemistandardFourierCovarianceStatement_iff` proves that this target is
equivalent to the following: under the same premise,
`IsWeylInvariant C (fam f)` holds for every `f`. The proof is
`isWeylInvariant_iff` of `RationalSemistandardInvariance`. `IsWeylInvariant` is a
predicate on the full dependent product `RationalSemistandardThetaSections a ha muM`,
so no support condition enters this comparison.

## The V.3.1 transport target

`rationalSemistandardFourierFiberCoefficient hG a ha muM d hdelta t A` is the
coefficient map `E_P^G` of the fiber of the family at `A`, namely
`rationalSemistandardFourierCoefficientMap` with the compact data, modular
comparison, split center and measure of the index `t.1`.
`rationalSemistandardFourierFiberForm` is the inverse-formal-degree V.2 product
`rationalSemistandardFourierProductForm` on the same fiber. These are the map and
form that appear in VII.1.1(ii), `rationalSemistandardFourier_pairing`.

`RationalSemistandardFourierFiberTransportStatement a ha muM d hdelta C` asserts the
following under `IntrinsicQuotientNormalization a muM d`. For every `t`, `q`,
`n : C.Lift t q` and actual inducing object `A`:

- the coefficient map at the target, applied to `C.fiberComparison t q n A v`, is
  the coefficient map at the source applied to `v`;
- the inverse-formal-degree products satisfy
  `⟪C.fiberComparison t q n A v, C.fiberComparison t q n A w⟫ = ⟪v, w⟫`.

This is Lemma V.3.1 in the models of the Fourier family. The degree factor of
the form is the reason for the measure premise. The closed comparison inside `C`
already gives the corresponding identities in the dynamic intrinsic models of V.3.
Those identities are part of `WeylSections.IsActualFamily`, through
`ActualConjugateLeviCoherence.PreservesCoefficientsAndForms`.
Transporting them to the fibers and measures of the Fourier family is a model
comparison that this module does not prove. The Library's
`WeylSectionComparisonData.CoefficientTransportStatement` and
`WeylSectionComparisonData.PairingTransportStatement` are related transports for
the source wave-packet coefficient map and pairing on smooth sections. This module
does not compare them with the present statement.

## Proved results

| Declaration | Content and proof |
| --- | --- |
| `rationalSemistandardFourierRepresentative_isSquareIntegrable` | Every actual inducing object of the orbit of a full index is a discrete series modulo the split center, for `muM t.1`; from `unitaryOrbitRepresentative_isDiscreteSeries` and `orbitRepresentative_isSquareIntegrable`. |
| `rationalSemistandardFourierFamily_pairing` | VII.1.1(ii) for one component of the full family, for an inversion-invariant ambient measure; `rationalSemistandardFourier_pairing` at the component's index and object. |
| `rationalSemistandardFourierFamily_eq_of_pairings` | The VII.1.1(ii) pairings against `f` determine a component; `rationalSemistandardFourier_eq_of_pairings`. |
| `rationalSemistandardFourierCovarianceStatement_iff` | The covariance target is `IsWeylInvariant C (fam f)` for all `f`, under the measure premise; `isWeylInvariant_iff`. |
| `rationalSemistandardFourierCovariance_of_fiberTransport` | For an inversion-invariant ambient measure, the V.3.1 transport target implies the covariance target. |
| `rationalSemistandardFourierCovariantSubmodule`, `mem_...` | The Schwartz functions whose family satisfies `IsWeylInvariant C` form a complex subspace; the comparison maps are linear. |
| `rationalSemistandardFourierProductRepresentation_eq` | The product action of `RationalSemistandardFourierFamily` is `rationalSemistandardThetaRepresentation`; reflexivity. |
| `translate_mem_rationalSemistandardFourierCovariantSubmodule` | The covariant subspace is stable under the two-sided translations `f(x) ↦ f(g2⁻¹ x g1)`; from `rationalSemistandardFourierFamily_translate` (VII.1.1(i)) and `IsWeylInvariant.action`. |
| `rationalSemistandardFourierCovarianceStatement_iff_submodule` | Under the measure premise, the covariance target says that the covariant subspace is everything. |
| `rationalSemistandardFourierFamily_mem_invariantSections_iff` | Comparison of carriers for one `f`, described below. |

The proof of `rationalSemistandardFourierCovariance_of_fiberTransport` is
Waldspurger's. Write `T = C.fiberComparison t q n A`. The target component is
characterized by its pairings (`rationalSemistandardFourierFamily_eq_of_pairings`
at `C.target t q n` and `C.representative t q n A`). Every vector of the target
fiber is `T v`, because `T` is bijective
(`WeylSectionComparisonData.fiberComparison_bijective`). Coefficient
preservation rewrites the pairing of `T v` against `f` as the pairing of `v`.
VII.1.1(ii) at the source turns this into `⟪v, fam f t A⟫`, and unitarity turns
that into `⟪T v, T (fam f t A)⟫`. The inversion invariance of the ambient measure
is a hypothesis of the imported VII.1.1(ii) and uniqueness theorems. The Haar
measure of the unimodular group of rational points satisfies it. The covariance
target itself does not assume it.

`rationalSemistandardFourierFamily_mem_invariantSections_iff` concerns one `f`
together with a supplied witness `hfin` that `fam f` lies in
`rationalSemistandardThetaSmoothSections a ha muM d`. With such a witness, the
element `⟨fam f, hfin⟩` lies in `rationalSemistandardThetaInvariantSections C`
exactly when `f` lies in the covariant subspace. The module supplies no such
witness. The general family is a map into the full product, and nothing here
asserts that its support is finite. That finiteness is part of Waldspurger's
VIII.1, which this module does not treat. The module also does not treat the
general wave-packet formulas or the VII.2.5 isometry and inversion.

## Dependencies

- `RationalSemistandardFourierFamily`: `rationalSemistandardFourierFamily`,
  `rationalSemistandardFourierFamily_translate`,
  `rationalSemistandardFourierProductRepresentation`.
- `RationalSemistandardFourierTransform`: `rationalSemistandardFourierCoefficientMap`,
  `rationalSemistandardFourierProductForm`, `rationalSemistandardFourier_pairing`,
  `rationalSemistandardFourier_eq_of_pairings`, `ModularNormalization`.
- `RationalSemistandardInvariantComparison`: `WeylSectionComparisonData`, its
  `fiberComparison` and `fiberComparison_bijective`, `target` and `representative`.
- `RationalSemistandardInvariance`: `IsWeylInvariant`, `isWeylInvariant_iff`,
  `IsWeylInvariant.action`, `rationalSemistandardThetaInvariantSections`.
- `RationalSemistandardComparisonHaar`: `SourceMeasure.IntrinsicQuotientNormalization`.
- `RationalSemistandardSpectralAction`: `rationalSemistandardThetaRepresentation`.
