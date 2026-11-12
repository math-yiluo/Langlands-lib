# Constructibility of the number of geometric connected components

Author: Worker 107.

`Langlands.AlgebraicGeometry.AlgebraicSpace.geometricFibreComponentsConstructible`
proves exactly the published proposition
`Langlands.AlgebraicGeometry.AlgebraicSpace.GeometricFibreComponentsConstructibleStatement`
in every universe `u`. For every commutative ring `B`, every quasi-separated
algebraic space over `Spec B` satisfying `FinitePresentationOverRing B X`,
and every natural number `n`, the locus where the geometric fibre has exactly
`n` connected components is constructible. The count is the extended-natural
cardinality of the connected components of the actual geometric-fibre point
space with its specified point topology. This includes `n = 0`.

The statement is Conrad's Lemma 5.1, printed p.13 of *Weil and Grothendieck
approaches to adelic points* (December 31, 2011), with the quasi-separatedness
convention and natural-number formulation explained in the unchanged
[statement documentation](GeometricFibreComponentsStatement.md). The registered
source is `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The present module composes published results; the following describes its
implemented proof.

First, `EtaleEquivalenceRelation.limitModelExistence` proves finite-stage
descent of an entire finitely presented étale scheme equivalence relation
over a small cofiltered affine-scheme limit. It descends the object and
relation schemes, the projections, their étaleness and all equivalence
relation laws. Its relation scheme may be nonaffine.

Next,
`SpaceLimitModelExistenceQuasiSeparatedReduction.spaceLimitModelExistenceQuasiSeparated_of_relation`
applies that theorem to an affine étale presentation of the original space.
It forms the quotient of the descended relation and compares kernel pairs
to obtain an actual base-change isomorphism with the original space. This
supplies a proof of `SpaceLimitModelExistenceQuasiSeparated` without an
additional premise.

Finally, `geometricFibreComponentsConstructible_of_limitModels` from
[GeometricComponentApproximation](GeometricComponentApproximation.md) applies
that model-existence result to the inverse system of spectra of the finite
integer subalgebras of `B`. Its stages are Noetherian and its limit is
`Spec B`. The constructed model has a quasi-compact locally finitely
presented étale surjective atlas and an actual comparison isomorphism.
Geometric component transport identifies each original fibre count with
the model count at the image point. The original `n`-count locus is therefore
the inverse image of the corresponding constructible locus over the
Noetherian model base. Constructibility is preserved by this scheme-map
inverse image. The Noetherian constructibility result used there is proved
by generic constancy on irreducible closed subsets and Noetherian induction,
as documented in [NoetherianGeometricComponents](NoetherianGeometricComponents.md).

The Lean term is precisely this composition of three theorems. Its type
is the original statement, with no model-existence argument or Noetherian
assumption on `B`. The statement's Lean/Markdown pair and import closure
are unchanged.
