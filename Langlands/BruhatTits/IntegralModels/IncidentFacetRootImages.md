# Actual root images for nonnegative incident-facet roots

This internal module uses equality of actual root fixer subgroups, without
requiring equality of their real supremum depth parameters. For two supplied
characterized neutral unramified zero-fixer models with a compatible split
integral torus, equality of the root fixers of nonempty affine-bounded subsets
makes the canonical integral root map and its actual residue base change
isomorphisms. The proof constructs the existing root-filtration models, applies
the imported equal-filtration model isomorphism, proves its ambient square by
generic rigidity, and identifies its hom with the canonical root map by full
target root representability.

The geometric comparison reuses `rootFixer_eq_of_nonempty_subset_facet`
from [UnramifiedIncidentRootImage](UnramifiedIncidentRootImage.md): a nonempty
subset of a facet has the whole facet's actual root fixer. The imported comparison for incident facets then gives equal
actual root fixers whenever the root is nonnegative on the displacement from
the face point to the incident facet point.

For actual maximal-unramified integers, the valuation is nontrivial and the
imported bounded-facet theorem bounds every affine functional on each facet.
The bounds pass to its subsets. Consequently the canonical integral and
residue root maps for every nonnegative root are isomorphisms at arbitrary
universe. The hypotheses retain the actual facet subsets and the actual
cocharacter displacement used in the unramified Lie-weight sign formula.

`integralRootIsoOfIncidentFacetsNonneg` packages the actual integral root
isomorphism. Its forward hom is definitionally the canonical integral root
map. Base change gives invertibility of the specified residue root map.

For a supplied reductive quotient of the target neutral special fibre, the
final three corollaries apply the imported invertible-residue-root results.
They prove smoothness of the full scheme-theoretic kernel of the original
source-root-to-target-quotient composite and identify both its differential
range and its actual schematic-image Lie range with the target positive
cyclic weight span. The action uses precisely the transported quotient
torus inclusion, and the cyclic tail uses the source torus's specialized
character. The schematic-image assertion uses full-kernel smoothness through
the imported comparison; it is not inferred from the image's smoothness.

This is a deduction from the imported model comparison, actual root models,
facet filtration comparisons and boundedness results. It does not assert the
strictly negative branch, smoothness of the full ambient incident kernel, or
the full weight-sign formula.
