# Eventual separatedness along the actual arithmetic integer diagrams

Authors: Worker 208 (complete Lean proof draft); Worker 1596 (source and
interface verification, explanatory Markdown and submission preparation).

`Langlands.Global.adelicSpreadEventualSeparation` proves exactly
`Langlands.Global.AdelicSpreadEventualSeparationStatement`, at arbitrary
universe `u`, by specializing relative separatedness descent to the
original arithmetic integer rings.

The private lemma `isSeparated_structure_baseChange_iff` compares the
relative `baseChangeMap` used by the generic limit theorem with the
structure map of the actual pullback. Postcomposition with the isomorphic
projection from the pullback of the identity identifies the first map
with `pullback.fst p a`. Precomposition by pullback symmetry identifies
this projection with `pullback.snd a p`. Separatedness is invariant under
both isomorphisms, giving an equivalence on the actual maps.

The private lemma `finiteTypeModel_separated_iff_stage` applies
`relativeSeparatednessDescent` to the structure map of a finite-type
model over a Noetherian ring, with target the identity of its affine
base. The source scheme is locally Noetherian by finite type, hence
quasi-separated; the stated quasi-compactness supplies the other
hypotheses. The actual spectrum cone is a limit by
`spectrumConeIsLimit`, constructed from the supplied algebra colimit.
The preceding map comparison and reindexing from opposite indices give
the equivalence for actual pullback structure maps.

For each arithmetic clause, `adelicSIntegersNoetherian` supplies
Noetherianity of the original outside-`S` integer ring.
`curvePlaceSIntegersOverIsColimit` or
`numberFieldSIntegersOverIsColimit` supplies the colimit of the actual
integer-ring diagram with vertex the original field. The structural
spectrum maps are definitionally the literal integer inclusions used in
the generic-fiber and level-model definitions. Applying the private
finite-type lemma therefore gives the statement without replacing any
model, ring, or map.

## Provenance and scope

This proof implements the statement's arithmetic specialization of Brian
Conrad, *Weil and Grothendieck approaches to adelic points* (December 31,
2011), printed pp.5–6, Theorem 3.4(2), property “separated,” and
Remark 3.5. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The private comparison lemmas are internal derived arguments for this
actual-ring specialization.

The proof retains arbitrary nonaffine finite-type models, including
initially nonseparated ones, and permits empty finite initial sets.
Function-field constants are arbitrary perfect fields, and the specified
finite rational-function extension need not be separable. It proves no
local compactness assertion or existence of a spread for a field scheme.
Its generic separation-descent and arithmetic-colimit dependencies have
their own independent acceptance and publication obligations.
