# Universe-general regular-atlas analytic targets

These internal proposition definitions extend the published
`PointManifold.RegularAtlasComparison` targets to a coefficient field
`k : Type u` with `RCLike k`. The source normed space, model space and parameter
space range independently over `Type v`, `Type w` and `Type z`.

`regularAtlasManifoldStatement k X d` asserts that every supplied covering
`RegularAtlas k X d` assembles into a real `C∞` manifold on the actual
`RingPoint k X k` carrier with the exact named `A.chartedSpace`. The topology is
the existing global-regular-function evaluation topology used by the atlas.
The model is `Fin d → k`, with real dimension `d * Module.finrank ℝ k`.

`regularAtlasFamilyCriterionStatement` asserts that maps from an arbitrary real
smooth manifold into that charted space are real `C∞` exactly when every global
regular-function value is real `C∞`. The source model with corners, topology,
charted-space structure and `IsManifold I ∞ M` hypothesis are explicit. The
statement does not replace the target manifold by this test property.
`regularAtlasComparisonStatement` is the conjunction of these two obligations.
Neither obligation constructs an atlas from algebraic smoothness.

The three `typeZero_iff` lemmas prove exact equivalence with the existing Type 0
propositions under the published chart/atlas conversion equivalences. The proof
uses the exact equality of the converted charted spaces and regular-function
tests. All three source universes remain free in these comparisons. There is
no new nonemptiness or positive-dimension hypothesis; empty spaces and `d = 0`
remain included in the statements.

Worker 94 adapted Worker 274's published target interfaces by making the
coefficient universe explicit, and proved the specialization equivalences.
The provenance is internal. The new arbitrary-universe analytic conjunction
is an exact proof target, not a theorem proved by this statement file; its
proof must establish chart transitions, manifold assembly and both directions
of the family criterion. Existing Type 0 proof targets and proofs are unchanged.
