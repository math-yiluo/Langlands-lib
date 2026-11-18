# Refined comparisons induced by actual atlas isomorphisms

This internal construction defines `Comparison.ofIso`: restrict both actual
full-order maps of a same-cover atlas isomorphism to a supplied principal
refinement, retaining their formal inverse equations. Its right refinement is
the supplied left refinement retargeted along the specified cover equality.

`Comparison.InducedBy` requires equality of whole integral formal test maps on
every coefficient algebra and every specified pair of original charts. The
right-hand side includes the actual original source transition followed by the
specified atlas isomorphism. This tests formal series, rather than evaluated
points. The restriction construction satisfies the criterion by the actual
atlas-map transition equation and the original transition cocycle.

`InducedBy.baseChange` proves that the actual coefficient-extended comparison
is induced by extension of the same actual isomorphism. The proof uses the
complete original-test comparison formula and the coefficient formulas for the
actual atlas map and transitions. The original chart selected at a reindexed
image is identified by `baseSource_sourceChart`. Independent selected sources
are retained, so the coefficient map need not be injective and may merge
principal generators.

The coefficient and acting rings have separate universes and arbitrary finite
coordinate types; covers may be infinite. This is internal compatibility of the
existing actual formal-map constructions, with no assertion of representability
or equality of global rational tensors from local data.
