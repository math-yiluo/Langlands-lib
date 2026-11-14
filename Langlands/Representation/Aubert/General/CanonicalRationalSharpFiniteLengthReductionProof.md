# Proof of the reduction of canonical Sharp finite length

Authors: Worker 274; Worker 29 and Worker 3640 (the supplied canonical
reduction draft and Task 3640, block (iv)); Worker 4216 (the conditional
finite-length assembly adapted here).

The module proves the exact published proposition
`Langlands.Aubert.General.RationalPointFamily.CanonicalRationalSharpFiniteLengthReductionStatement.{u, v}`
from `CanonicalRationalSharpReductionStatements`, by the theorem
`canonicalRationalSharpFiniteLengthReduction`. The two inputs, in order, are
`DynamicInductionFiniteLengthStatement.{u, max (u + 1) v}` and
`DynamicJacquetFiniteLengthStatement.{u, max (u + 1) v}`. The conclusion is the
whole `CanonicalRationalSharpFiniteLengthStatement.{u, v}`. The proof has no
other premise and does not prove either input or the unconditional conclusion.

## Implemented proof

The proof introduces the two dynamic hypotheses and the canonical target's
field, connected reductive group, maximal split torus, generic cocharacter and
linear order. It installs the canonical `pointTopology` and the same published
affineness, smoothness, local compactness, nonarchimedean and Hausdorff
instances used in the target. It installs the published
`simpleRelativeRootFintype` using `relativeRootSystem`.

For each standard subset `J`,
`standardInductionJacquet_preservesFiniteLength_of_dynamic` from
`RationalStandardFiniteLength` applies the two hypotheses to the actual
normalized induction and Jacquet functors. Its structural inputs are the
published `standardCocharacter` and
`canonicalStandardUnipotent_isClosed`. Its subgroup transport identifies the
standard parabolic, Levi and unipotent subgroups with those of a dynamic
cocharacter. Composition gives finite-length preservation of each actual
induction–Jacquet term.

`sharpFiniteLengthTarget_of_inductionJacquet` from `SharpFiniteLength` then
proves the exact generic target at the canonical structural data. That helper
proves finite length of each homogeneous degree by its finite product of
terms, and of the actual terminal cokernel by the surjective terminal
projection. The cokernel is taken at the existing removed-root degree
`|S| - |I|`. The argument applies to every finite-length smooth `E`, without a
support-category hypothesis, and includes empty simple-root sets.

The field universe `u` and carrier parameter `v` remain independent; the
dynamic hypotheses retain carrier universe `max (u + 1) v`. All canonical
target binders, topologies and instances are unchanged. No statement pair or
imported pair is edited.

## Provenance and scope

This is an internal proof between published targets, with no new translation
of the literature. The statement's Markdown records the literature content:
Aubert (1995), Corollaire 3.9 (a), printed p. 2189, and Renard VI.6.2 and
VI.6.4, printed pp. 178–179. This module establishes only the conditional
finite-length reduction.

Worker 29 and Worker 3640 supplied the canonical reduction draft. The present
proof specializes the conditional assembly of Worker 4216 directly to the
canonical data using published helpers, rather than importing the pending
rational reduction and canonical bridge. Task 6581
(`3545b661-3e38-40c6-b8aa-721a7e9adba9`) retains the rational reduction,
Task 6425 (`d7477c1e-06c2-43ec-9035-3eb6b594058b`) retains the canonical
bridges, and Task 4216 (`0da1c37e-a39a-42e1-b90d-135db6c6e5c3`) retains
unconditional rational Sharp finite length. The generic finite-product and
quotient proof is the published work of Worker 508, adapting Worker 164;
the dynamic-to-standard finite-length transport is the published work of
Worker 749. All are reused by declaration name. The owners of the two dynamic
input targets retain their proof obligations.
