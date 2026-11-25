# Proof: homomorphisms with commutative image from a semisimple Weil restriction

This module proves `Langlands.GroupScheme.WeilAbelianImageTrivialityStatement.{u}` (module
`Langlands.GroupScheme.Reductive.WeilAbelianImageTrivialityStatement`):

- `Langlands.GroupScheme.weilAbelianImageTriviality : WeilAbelianImageTrivialityStatement.{u}`.

## Proof

After introducing the quantified data and hypotheses, the theorem is
`WeilAbelianImage.app_eq_one G' c hc hred hss X x` from module
`Langlands.GroupScheme.Reductive.WeilAbelianImageTriviality`. That module's Markdown describes the
argument:

1. Every point of the reductive group `G'` with semisimple geometric fibres lies, after
   restriction to each member of some fppf cover of its test scheme, in the abstract commutator
   subgroup of the group of points there, i.e. it is locally a finite product of commutators
   (`RelativeDerived.LocallyCommutator`, supplied by `relativeSemisimpleFppfPerfect`). A
   homomorphism whose values commute kills that whole subgroup, and the points of `M` are
   separated by the fppf cover, so the homomorphism is trivial on the original point. Applied to
   `c` composed with `embNat`, this gives triviality on the diagonal factor, the image of
   `embNat`, over all `B ⊗[A] T`-algebras.
2. If `B ⊗[A] X` has a complete orthogonal family of graph idempotents, every point of the Weil
   restriction over `X` is a product of components, each a diagonal-factor point after a change of
   `B ⊗[A] T`-structure through the graph of an algebra map `B → X`; so `c` is trivial over `X`.
3. `B` splits over an fppf cover of `Spec A` (rank decomposition and Mathlib's
   `Algebra.IsFiniteSplit.exists_tensorProduct_of_etale`), and points of `M` over `X` are separated
   by the pullback of that cover, so `c` is trivial over every `X`.
