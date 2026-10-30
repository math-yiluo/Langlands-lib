# Continuous-map gluing on finite full-domain covers

Worker 56 constructs unique gluing of compatible continuous maps on the
loci of a supplied finite cover by actual full affinoid domains. The namespace
is `Langlands.Analytic.PresentedAffinoidAlgebra.Domain.FiniteCover`.

## Inputs and provenance

The field `K : Type u` is complete, normed and ultrametric. Its valuation
may be trivial. The base `A : PresentedAffinoidAlgebra K` and all domain
algebras are the published finite positive-polyradius closed Tate quotients.
A supplied full domain `V : Domain K A` contains an actual bounded structural
map, a closed locus in `BanachSpectrum A`, its exact structural image and the
full affinoid-test universal property. A supplied `c : FiniteCover V` retains
the component full domains, their actual bounded restrictions to `V`, and
pointwise coverage of `V.locus`.

The registered original is V. G. Berkovich, *Non-archimedean analytic spaces*
(Trieste lectures, 2009), literature ID
`berkovich-2009-trieste-analytic-spaces`, PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
Definition 1.2.5 and Fact 1.2.6 on printed/PDF p.4 give the evaluation
topology and spectrum compactness for a nonzero Banach ring. Definition
2.2.1 on p.9 supplies the full-domain inputs. The imported
`DomainTopology` uses the independently proved compact Hausdorff spectra,
also including empty zero-ring spectra, to construct the actual finite
spectrum-cover quotient map.

This unit is an internal consequence of that published quotient map.
The source does not separately state the present gluing equivalence.
Mathlib's `Topology.IsQuotientMap.lift` descends a continuous map constant
on quotient fibers; `lift_comp` proves its defining restriction identity.
No new analytic representation theorem is used.

## Compatibility and restriction

The target `Y : Type v` is any topological space in a universe independent
of the field. `Compatible c g` is a proposition about a family of continuous
maps `g i : C((c.obj i).locus, Y)`. It requires
`g i x = g j y` whenever `x` and `y` have the same underlying point of
`BanachSpectrum A`. This compares every pair of component loci at their
actual set-theoretic overlap. It needs no representing algebra for that
overlap.

`restrict c f i` composes a continuous map on `V.locus` with the actual
domain arrow's locus map. `compatible_restrict` follows because those
locus maps preserve the underlying base point.
`ext_of_restrict_eq` proves that equality of all restrictions determines
the original continuous map: every target point has a preimage in the
published total map from the component spectra.

## Construction and laws

`spectrumFamilyMap c g` assembles the composites of `g i` with the
component structural spectrum-to-locus maps on the disjoint union

`Σ i : Fin c.size, BanachSpectrum (c.obj i).algebra`.

Continuity holds on each summand. If the family is compatible,
`spectrumFamilyMap_factorsThrough` proves that this map is constant on
every fiber of `c.totalMap`: equal target-locus points have equal
underlying base-spectrum points.

`glue c g hg` applies the published quotient-map property and Mathlib's
continuous quotient lift. `glue_apply_spectrum` is the quotient lift's
restriction identity on a component's actual spectrum. Surjectivity of
that component's structural map then gives `restrict_glue` directly on
its locus.

`glue_restrict` and `glue_unique` use the proved restriction extensionality.
They give both inverse laws of `gluingEquiv`, a constructed equivalence
between `C(V.locus, Y)` and the subtype of compatible continuous families
on the component loci. The inverse is the constructed quotient lift.
The existence of a glued map is proved, not included as an assumption.

For any continuous `p : C(Y, Z)`, where `Z : Type w` has a third
independent universe, `compatible_postcomp` proves compatibility after
postcomposition. `glue_postcomp` follows from uniqueness and says that
gluing commutes with postcomposition by `p`.

## Scope and empty cases

There is no nonempty-target, positive-cover-size or separation assumption
on `Y` or `Z`. All constructions also apply to an empty cover, for which
the already published coverage property forces `V.locus` to be empty.
No choice of a point of `Y` is needed.

These are continuous maps on actual domain loci. The unit constructs
neither gluing of quotient-algebra sections nor an analytic structure
sheaf, an intersection representation, a general analytic atlas or an
étale site. In particular, it does not discharge the separate rational
algebra gluing or analytic-space construction obligations.
