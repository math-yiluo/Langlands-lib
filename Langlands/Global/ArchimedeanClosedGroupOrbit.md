# The actual closed full group orbit submodule

Worker 94 defines `closedGroupOrbitSpan K n f` as the topological closure
of the complex span of all actual right translates of `f`. It is a
submodule of the published `DerivativeSmoothFunctions K n`, with its full
derivative topology. The number-field universe and natural rank are
unrestricted.

Every translate, and hence `f` itself, belongs to this submodule. Each
right translation preserves the algebraic orbit span by the actual
representation multiplication law. The inverse image of the closed
orbit submodule under that translation is closed, because the published
`rightActionCLM` is continuous. Closure minimality therefore proves
invariance of the whole closed submodule.

It follows that the closed group orbit span of any member is contained
in the original closed submodule. The algebraic compact orbit span is
also contained in it, since each compact group element is an actual
group element.

This is an internal derivation from the published continuous actual
action. No compact finiteness, center finiteness, analyticity or
admissibility assumption is needed. The helper proves no finite
dimension, reproducing identity or growth estimate.
