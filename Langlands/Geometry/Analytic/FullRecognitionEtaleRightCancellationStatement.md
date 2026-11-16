# Strong étale right cancellation over all affinoid pieces

`AffinoidAtlasPresentation.StrongHom.EtaleRightCancellationStatement K`
is a proposition about two composable actual strong maps between the
constructed saturated presentations of three affinoid atlas presentations.
If the second map and the specified saturated composite satisfy the
Library's `IsEtaleAllPieces`, then the first map must satisfy that same
predicate.

The ground field is any complete ultrametric normed field. Its universe,
the spaces' universe and the atlas indices' universe remain independent.
The three presentations use the same space and index universes, as in
the imported strong composition API. There is no global Hausdorff,
nontrivial valuation or strict affinoid hypothesis.

Both assumptions and the conclusion use the all-pieces predicate defined
in `FullRecognitionEtaleComposition`. At each source point it requires an
open neighborhood on which unramifiedness and flatness hold over all
recognized affinoid pieces of suitable finite neighborhoods. In
particular, the first map is not assumed quasifinite. Producing its
finite neighborhoods is part of the proposed result.

## Provenance

This is a derived prerequisite for transporting étale maps into the
localized étale site; it is not a literal restatement of Berkovich's
Corollary 3.3.9. In *Étale cohomology for non-Archimedean analytic spaces*
(1993), §3.3, printed page 63, that corollary assumes **both** morphisms
quasifinite, the composite étale and the second morphism unramified.
Its proof on printed page 64 factors the first morphism through its
graph, using the open diagonal of an unramified map and base change of
the étale composite. The following paragraph states the resulting
étaleness of every morphism between étale objects over a fixed base.
These are retained PDF pages 60–61.

The present proposition expresses the fixed-base cancellation consequence
with the Library's stronger all-pieces predicates. A proof must still
justify the geometric constructions for the actual strong maps and
recognized domains, and establish the all-pieces conclusion. The cited
corollary cannot be invoked while silently dropping its quasifiniteness
premise. In particular, ring-map cancellation alone does not discharge
this proposition.

This module defines the statement only. It neither proves it nor asserts
the localized cancellation property, which has a separate statement and
transport obligations. Together with the localized transport, this is
intended to supply the fact that arrows between étale objects in the
geometric-point proof are étale. The exact geometric-point statement
remains an additional proof obligation.
