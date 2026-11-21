# Proof of target-local finiteness

Module `Langlands.Geometry.Analytic.FullRecognitionFiniteTargetLocalityProof`.

`Langlands.Analytic.AffinoidAtlasPresentation.StrongHom.finiteOverTargetLocality`
proves `FiniteOverTargetLocalityStatement.{u, v, w} K`. For a strong map `g`
between actual saturated analytic presentations and open subsets `V` and `U`
with `g(V) ⊆ U`, suppose each point of `U` has a finite family of recognized
target affinoids in `U`, all containing the point, whose union is a neighborhood.
If each family member has a recognized full preimage in `V` with finite Banach
pullback, then `g.IsFiniteOver V U`. In particular, the conclusion supplies a
recognized full preimage and finiteness of the actual bounded pullback for
**every** recognized target affinoid `W` in `U`, including one spanning several
members of the families.

## Implemented proof

The theorem applies `finiteOverTargetLocality_of_descent` from
[`FullRecognitionFiniteTargetLocalityOfDescent`](FullRecognitionFiniteTargetLocalityOfDescent.md)
to `PresentedAffinoidAlgebra.finiteAffinoidAlgebraDescent` from
[`GeneralizedAffinoid.FiniteAffinoidAlgebraDescent.Proof`](GeneralizedAffinoid/FiniteAffinoidAlgebraDescent/Proof.md),
discharging the effective descent premise.

The first import refines each `W` into a finite full-domain cover subordinate
to the families and constructs the finite Banach preimage models and their
overlap data. It proves Hausdorffness of the literal preimage
`V ∩ g⁻¹(W.locus)` from the neighborhood families, without assuming either
ambient space is Hausdorff. Given an effective realization of the overlap data,
it recognizes that literal preimage and identifies the descended finite map
with the actual bounded pullback via equality on original chart restrictions.
The second import provides the effective realization on every such full-domain
cover by constructing a finite generating tuple of matching elements.

The proof adds no hypotheses to the target: the field, space and index
universes are independent; the complete ultrametric field may be trivially
valued, and no strictness condition is imposed on the positive finite polyradii.
Only the union of the members at a point is required to be a neighborhood.

## Provenance

This is the relative-open finite-morphism implication of Berkovich,
*Étale cohomology for non-Archimedean analytic spaces* (1993), Lemma 1.3.7(a)
implies (b), printed pp. 27–28 (PDF pp. 24–25). The descent step implements
the finite-algebra application of Kiehl's theorem (§1.2, printed p. 15,
including Remark 1.2.1(ii); see also Lemma 1.2.12, printed p. 20).
Registered source: `berkovich-1993-etale-cohomology`.
