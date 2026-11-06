# From Laurent and all-unit covers to strict rational ideal descent

This internal module defines the uniform binary Laurent and all-unit
standard rational ideal-descent inputs. It proves that these inputs imply
effectiveness on every finite strict rational point cover. It does not
prove either input in this module.

The standard-cover proof follows the geometric induction already used by
the Library's scalar standard rational descent proof. The implemented ideal
diagram chase uses the separately proved ideal refinement and Laurent-split
reductions.

First induct on the number of entries of the standard tuple, then on the
number of entries that are not units in the actual base algebra. An empty
tuple has no local conclusion to prove. If every entry is a unit, apply
the explicit all-unit input. Otherwise reindex a chosen nonunit entry to
the last position; equal-locus inclusions exhibit the reindexed standard
cover as an actual refinement of the original one.

Choose the Library's uniform nonzero scalar threshold below the maximum
tuple value at every spectrum point, and split the last entry divided by
that scalar into its actual upper and lower Laurent domains. Over the
upper branch, the shortened tuple still has no common zero and its
standard cover refines the pulled original cover. The outer induction
therefore supplies effectiveness there. Over the lower branch the chosen
last entry becomes a unit. The injective comparison between the finite
sets of remaining nonunit entries misses this entry, so their cardinality
strictly decreases; the inner induction supplies effectiveness.
The assumed binary input and the proved Laurent-split ideal chase recover
effectiveness before the split.

For an arbitrary finite rational cover, apply the published finite standard
rational refinement theorem. Choose the actual rational inclusions from
its locus containments, prove effectiveness on that standard cover, and
transfer it back using ideal refinement. A universe lift of the original
finite ordinal allows use of the existing refinement theorem without
changing any mathematical indices or algebras.

The proof uses the actual stored quotient algebras and bounded maps, with
the explicit contracted ideal supplied by the ideal-refinement and
Laurent-split theorems. The coefficient field's nontrivial valuation is
explicit; nonreduced and zero algebras, empty spectra, and empty finite
rational covers remain included. The provenance is an internal adaptation
of the Library's scalar covering induction and its already proved
geometric refinement lemmas.
