# The groupoid of actual line bundles

This module constructs `PicardGroupoid X` as the core of the published category
`LineBundle X`. Its objects are actual locally free sheaves of rank one, and its
arrows are their isomorphisms. Pullback is the core of the published line-bundle
pullback functor. The unit and composition comparisons come from the ordinary
pullback comparisons on sheaves of modules.

The coherence proofs forget first the core and then the full subcategory of
locally free sheaves. They reduce to Mathlib's three coherence lemmas for module
pullback. These data define `PicardGroupoid.pseudofunctor` on schemes and its
precomposition `PicardGroupoid.relative f` with the actual base-change family
`relativeSpace f`.

This is an internal construction from existing definitions. It implements the
underlying groupoid-valued pseudofunctor in Artin, *Versal deformations and
algebraic stacks* (1974), Appendix item 2, printed pages 186–187, registered as
`artin-1974-versal-deformations-algebraic-stacks`. It does not yet assert descent,
algebraicity, smoothness of automorphism groups, or representability of its
sheaf of isomorphism classes. No properness or flatness hypothesis is needed
for this construction.
