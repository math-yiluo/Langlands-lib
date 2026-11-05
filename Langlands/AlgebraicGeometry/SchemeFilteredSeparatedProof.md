# Proof of separatedness descent over the original ring system

`ringSystemSeparatednessDescent` proves exactly
`Langlands.AlgebraicGeometry.SchemeLimitModel.RingSystemSeparatednessDescent`
in arbitrary universe `u`. It conjoins the spectrum, original initial-ring,
and source finite-presentation forms proved in the same file.

The source is Brian Conrad, *Weil and Grothendieck approaches to adelic
points* (December 31, 2011), printed pp. 5–6, Theorem 3.4(2), separatedness
clause. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
Conrad's finite-presentation convention on printed p. 5 corresponds to
locally finite presentation, quasi-compactness and quasi-separatedness of
the model structure maps. The first two forms are derived strengthenings;
the third gives the source separatedness clause.

Worker 105 authored the Lean proof, reused here unchanged from the shared
proof-only draft. Worker 148 checked its dependencies and exact scope,
expanded this explanation, and prepared the submission.

`spectrumSeparatednessDescent` applies `relativeSeparatednessDescent`
to `spectrumDiagram`, its actual `spectrumStructure` transformation,
`spectrumCone` and the derived `spectrumConeIsLimit` witness. The
compatibility equations are `spectrumCone_compat`. Filteredness of the
algebra index supplies cofilteredness of the spectrum index; the
spectrum objects and base are affine. For arbitrary models `X` and `Y`
over `Spec R`, the relative hypotheses are exactly quasi-compactness
and quasi-separatedness of `f.left` and quasi-compactness of `X.hom`.
The theorem identifies separatedness of the actual `baseChangeMap`
along `spectrumBaseMap` with its counterpart at some stage. Replacing
the opposite-category stage by its `unop`, and using `op` in the reverse
direction, gives precisely the stage algebra quantifier in the proposition.

`initialRingSeparatednessDescent` specializes this result to the
constructed `initialRingAlgebraDiagram` and `initialRingAlgebraCocone`.
Its algebra-colimit witness is derived from the original cocone by
`initialRingAlgebraCoconeIsColimit`. The structure maps reduce to
exactly `Spec.map (c.ι.app j₀)` at the colimit and
`Spec.map (F.map j.hom)` at a stage `j : Under j₀`. Thus the conclusion
contains an actual arrow from the original chosen stage, with its
original ring and map. No transition-injectivity assumption is used.

`finitePresentationInitialRingSeparatednessDescent` uses `Over.w f`
to identify the composite structure map with `X.hom`. It derives
quasi-compactness of `f.left` from that of the composite and
quasi-separatedness of `Y.hom` using `QuasiCompact.of_comp`, and
quasi-separatedness of `f.left` from that of the composite using
`QuasiSeparated.of_comp`. Together with the given quasi-compactness of
`X.hom`, these supply all three relative hypotheses of the original
initial-ring result. The six model finite-presentation hypotheses remain
exactly those of the published target; no relative hypothesis on `f`
is added. The final theorem conjoins the three proved forms.

All forms retain arbitrary nonaffine and possibly nonseparated models
under their displayed hypotheses, arbitrary filtered ring systems and
noninjective transitions. The proof submission contains only this new
proof pair and imports the unchanged published target and
`relativeSeparatednessDescent` by Lean name. Other properties of
Theorem 3.4(2), the other clauses of that theorem, and whole-paper
obligations remain with the parent task.
