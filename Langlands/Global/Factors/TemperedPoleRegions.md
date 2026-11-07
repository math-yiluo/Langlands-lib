# Pole bounds for certified tempered pair L-polynomials

This internal adapter supports the proof of Henniart (2000), Corollaire 2.3,
whose exact target is
`Langlands.ClassField.Global.RelativeWeilGroup.AssociatedTemperedFactorStatement`.
Its constructions use the published analytic temperedness and JPSS pair-factor
interfaces.

`TemperedLanglandsDatum.single` places an irreducible tempered representation
of positive rank in a single block with exponent zero. Its exponent ordering
is vacuous because the indexing type has one element.
`TemperedLanglandsDatum.exists_zero_presentation` proves that this construction
presents every equivalent target in the saturated carrier universe. The actual one-block
normalized induction equivalence and the identity of the zero twist give an
equivalence of the standard module with the target. Its surjective intertwiner
certifies the Langlands quotient.

`IsLanglandsPairLPolynomial.symmetric_of_tempered` first realizes the two
irreducibles in the prescribed block universes, using
`padicIrreducibleSmoothSmallRealization`. It applies the universal clause of
the Langlands pair certificate to the two zero-exponent presentations, and
transports the resulting symmetric L-polynomial certificate along their actual
representation equivalences.

`temperedBlockInduction_poleFree` rewrites arbitrary positive block sizes as
successors and applies the closed theorem `Langlands.RankinSelberg.temperedLFactor`,
retaining its nonvanishing conclusion. For an arbitrary tempered irreducible
pair, `IsPadicSymmetricLPolynomial.poleFree_of_tempered` uses
`Langlands.Classification.temperedBlockExhaustion` to obtain actual normalized
induction realizations. It transports the supplied polynomial to those
realizations and uses uniqueness to identify it with the pole-free polynomial.
`IsLanglandsPairLPolynomial.poleFree_of_tempered` composes these two adapters.
The two representation and block carrier universes remain independent.

`IsAutomorphicPairLPolynomial.poleFree_of_tempered` transports this conclusion to
the classes of any two supplied actual irreducible admissible tempered objects.
It uses the equivalences in the class certificate, and class equality as
equivariant representation equivalence.
`IsSmoothDual.tempered_representative` applies the proved
`PadicField.TopologicalData.IsTempered.smoothContragredient` and transports
temperedness along the equivalences in the smooth-dual relation.

Finally,
`Langlands.Global.FactorSeparation.certifiedAutomorphicPoleRegions_of_tempered`
proves `CertifiedAutomorphicPoleRegions` for those two objects. Every root of
the original polynomial has norm at least one. For such a nonzero argument
`z`, the reflected argument `q⁻¹ z⁻¹` has norm strictly less than one because
`q > 1`. The polynomial for every pair of smooth dual classes is nonvanishing
there by the preceding temperedness and pole-free results. This works for
every self-dual Haar measure and every polynomial certificate supplied to
`CertifiedAutomorphicPoleRegions`.

This is a derived adapter; it does not assume a Langlands correspondence or
the global associated-gamma statement. The singleton datum is an internal
construction from the published Langlands datum definition; the resulting
separation is the tempered case of the representation-side argument of
Henniart (1986), Proposition 4.5(ii), printed pp.160–162. Henniart (2000),
Corollaire 2.3, printed p.445, is its intended application. This file proves
the automorphic pole-region input only, not the global corollary.
