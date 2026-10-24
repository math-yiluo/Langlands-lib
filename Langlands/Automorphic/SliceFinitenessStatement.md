# Finiteness of actual smooth infinite slices

Author: Worker 94. Module: `Langlands.Automorphic.SliceFinitenessStatement`.
The combined proposition is `Langlands.Automorphic.SliceFinitenessStatement`.
It has the full parameters `K : Type u`, `[Field K]`, `[NumberField K]`,
and `n : ℕ`, including rank zero. It is the conjunction of two statements
about the existing concrete function spaces and actions.

## Center-family evaluation

`CenterFiniteFamilyEvaluationStatement` says that for every family
`F : SmoothSliceFamily K n`, the published `IsCenterFiniteFamily K n F`
implies `ArchimedeanGL.IsCenterFinite K n (F b)` for every finite adelic
matrix `b`. The premise is finite complex dimension of the orbit of the
entire family under one center element applied simultaneously to all slices.
The conclusion concerns the orbit of one smooth function under the same
actual enveloping-center differential action.

This is a one-way implication. It neither replaces the simultaneous family
condition with separate slice conditions nor asserts the converse. In the
adelic application the family remains `smoothSliceFamily K n f`, and
`Automorphic.IsCenterFinite K n f` remains its existing simultaneous condition.
The already published equivalence with a single finite-codimensional
annihilating ideal, in `Automorphic.CenterFinite`, is unchanged.

## Infinite-subgroup finiteness

`SmoothSliceSubgroupFiniteStatement` quantifies over every subgroup
`U : Subgroup (InfiniteAdelicGL K n)` and every actual smooth adelic function
`f : SmoothRationalFunctions K n`. Its premise is the existing
`IsInfiniteFinite K n U f.val` on the continuous adelic carrier. For every
finite adelic matrix `b`, its conclusion is finite complex dimension of the
orbit of `smoothInfiniteSlice K n b f` under
`(ArchimedeanGL.smoothRightAction K n).comp U.subtype`.

The slice is the genuine function `a ↦ evaluate K n f.val (pair K n a b)`.
Both actions use right translation: an element `k` of `U` replaces `a` by
`a * k`. The conclusion is stated on `ArchimedeanGL.SmoothFunctions`, with
its existing smoothness predicate, rather than only on unbundled functions.
There is no compactness assumption on `U`, common finite-level assumption,
center condition, growth premise, or extra equivariance premise. Taking
`U = standardInfiniteCompact K n` will give the group-finiteness premise
needed by the separate compact-group-to-differential bridge.

## Internal derivation and remaining proof

These are internal consequences of the published algebraic interfaces,
not reproductions of a theorem from the literature. The definitions used are
from `Automorphic.CenterFinite`, `Automorphic.FiniteVectors`,
`Automorphic.Smooth`, `Global.ArchimedeanCenterFinite`, and
`Representation.FiniteVectors`. Their imported meanings are unchanged.
No additional source theorem is invoked for these two implications.

A proposed proof of the first part uses evaluation at `b` as a linear
intertwiner from the center family representation to the single-function
center representation, then applies finite-vector preservation under an
intertwiner. For the second part, the injective inclusion of smooth adelic
functions into continuous adelic functions transfers the given orbit
finiteness to the smooth carrier. The slice map then intertwines the
restricted infinite-factor right actions by the adelic pair multiplication
law, so its image has finite orbit. Constructing these intertwiners and
proving the two implications are proof obligations. This Lean file only
defines the three propositions and checks the combined parameter telescope.

The module proves no compact-group-to-differential implication, joint
center/compact finiteness, reproducing-kernel theorem, or derivative-growth
theorem. It does not change any automorphic condition or infer finiteness
of an entire family from finiteness of its separate slices.
