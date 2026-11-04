# Closed immersions for full-adele points of a fixed model

`Langlands.Global.AdelicFixedModelClosedImmersionStatement` asserts the following
in an arbitrary common universe. Let Y be a finite-type model over the actual
outside-S integer ring, let X be a model over the same ring, and let f : X → Y
be a closed immersion over that ring. Actual postcomposition with f is a closed
embedding on actual points over the full adele ring, equipped with the published
final topologies from all arithmetic levels containing S.

The two clauses concern the actual curve-place adele ring and the full
number-field adele ring. The number-field clause retains every infinite
completion. The curve clause uses the original specified k → RatFunc k → F
scalar tower and `FunctionField k F`; no separability or finite-constant
hypothesis is imposed. Either initial finite set S may be empty.
Finite type of Y is stated as local finite type plus quasi-compactness of its
structure morphism. No affineness, separatedness or quasi-separatedness is
assumed. A closed immersion into Y makes X finite type as well.

## Provenance and scope

Brian Conrad, *Weil and Grothendieck approaches to adelic points*, December 31,
2011, printed p.9, Section 4 opening paragraphs, asserts that closed immersions
induce closed embeddings for the full final adelic topology, including before
imposing separatedness. The product-level closed-embedding assertion is used
immediately before this, in Corollary 3.7 on the same page.
Registered source: `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

This is a derived fixed-model form of that passage. The broader curve scope
(arbitrary constants, inseparable extensions and empty S) is intentional:
closed factorization is detected by the injective level-to-adele ring maps,
and the arithmetic-level closed embeddings require neither local compactness
nor finiteness of residue fields. The point spaces are the actual relative
scheme morphisms and the topologies are already defined independently in
`AdelicFixedModelCocone`, using the original arithmetic level products.

This unit states the closed-embedding property and supplies no proof.
Comparison with generic-fiber adelic points, eventual descent of a generic-fiber
closed immersion, and whole-paper coverage remain separate obligations.
