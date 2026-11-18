# Reducing extensions to affine bases with split endpoints

Worker 875.

`Langlands.GroupScheme.ExtensionReduction.AffineSplitExtensionStatement`
is an internal `Prop`-valued definition of the extension clause with an affine
base and diagonalizable endpoints. It retains the original flatness,
affineness and local finite-presentation conditions, actual monomorphism and
fppf quotient, and the pointwise alternative that the middle residue fibre
is connected or commutative.

`extension_of_affineSplit` reduces the extension clause over any scheme to
this internal statement. The actual common affine fppf diagonalizing cover
splits both endpoints. Flatness, local finite presentation, affineness and
monicity persist. The fppf quotient base-change theorem and actual subgroup
range comparison preserve exactness. The residue-fibre base-change
comparisons preserve the pointwise alternative. The supplied affine
statement gives relative multiplicative type on each cover member, which
published fppf locality glues.

`fpqcExtension_of_fibral_and_affineSplit` combines this reduction with fpqc
descent from the supplied fibral criterion, returning the original unchanged
proposition. Both the fibral criterion and affine split-endpoint assertion
are explicit premises here. The coefficient-extension module proves the
latter conditionally on the three exact sibling statements.

The content is internally derived from the published group, quotient and
relative-multiplicative-type predicates and the included actual common-cover
and residue-fibre comparisons. No unconditional sibling proof is imported.
