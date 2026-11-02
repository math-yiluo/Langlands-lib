# Spectrum embedding for every full presented affinoid domain

Authors: Worker 135 and Worker 74.

`Langlands.Analytic.PresentedAffinoidAlgebra.Domain.spectrumEmbedding` proves
the published `Domain.SpectrumEmbeddingStatement` at every universe `u`.
For every complete ultrametric normed field `K : Type u`, actual finite
positive-polyradius presented affinoid algebra `A`, and `U : Domain K A`,
the conclusion is `Topology.IsClosedEmbedding U.spectrumMap`. This is the
stored structural spectrum map induced by `U.baseMap`.

The proof establishes injectivity and then applies the theorem that a
continuous injection from a compact space into a Hausdorff space is a
closed embedding. The spectrum topology instances come from the imported
Library spectrum results, and continuity is part of `U.spectrumMap`.

Let `x` and `y` be points of the spectrum of `U.algebra` with the same
structural image in the spectrum of `A`. The unconditional theorem
`PresentedAffinoidAlgebra.pointAmalgamation` realizes them by bounded
`K`-algebra maps `f` and `g` into one complete ultrametric normed field
`L : Type u`. These maps satisfy

```text
f.comp U.baseMap = g.comp U.baseMap,
∀ b : U.algebra, ‖f b‖ = x b,
∀ b : U.algebra, ‖g b‖ = y b.
```

The construction `finiteJointImage f g` supplies an actual finite presented
affinoid `D.algebra`, bounded maps `D.left` and `D.right` from `U.algebra`,
and an injective bounded map `D.embed` into `L`. Their composites with
`D.embed` recover `f` and `g`. The theorem `FiniteJointImage.comp_eq`
uses this injectivity to show that `D.left` and `D.right` have the same
composite from `A`.

The common composite has spectral image in `U.locus`: every point of
`D.algebra` pulls back along `D.left` to a point of `U.algebra`, and its
structural image belongs to that locus by `U.represents.hasImageIn`.
The unique factorization clause of the full representation property,
tested on the finite affinoid `D.algebra`, therefore gives
`D.left = D.right`. Composing with `D.embed` gives `f = g`. The two exact
norm identities now imply `x b = y b` for every `b`; spectrum
extensionality proves `x = y`.

No point of `D.algebra` is chosen, so the argument also covers empty
spectra. All universes and hypotheses of the target are retained,
including arbitrary positive real polyradii, trivial valuations,
nonreduced algebras and zero algebras. The proof needs neither a closed
image of `D.embed` in `L` nor an inverse norm bound. It introduces no
rational-presentation, strictness, nonzero or spectral-injectivity
hypothesis.

This is an internal derivation from the Library's full domain
representation, finite joint-image construction, unconditional
point-amalgamation theorem and spectrum topology. The target's paired
Markdown records its provenance in Berkovich's Trieste lectures (2009),
Definition 2.2.1 on p. 9 and Fact 2.2.3(i) on p. 10. The implemented proof
uses the Library's presentation category and the common-field argument
above. It does not construct arbitrary domain intersections or identify
that category with a separate category of abstract Banach algebras.

Worker 135 supplied the finite-test construction and domain reduction;
Worker 74 contributed the completed-residue and common-field proof route.
