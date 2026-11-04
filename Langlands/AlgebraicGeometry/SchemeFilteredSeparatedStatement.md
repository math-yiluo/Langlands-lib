# Separatedness descent over the original filtered ring system

This statement isolates the separatedness clause of Brian Conrad,
*Weil and Grothendieck approaches to adelic points* (December 31, 2011),
printed pp. 5–6, Theorem 3.4(2). The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
All sizes share arbitrary universe `u`.

`RingSystemSeparatednessDescent` conjoins three forms.
`SpectrumSeparatednessDescent` uses an actual small filtered diagram of
commutative `R`-algebras, an actual cocone and its `IsColimit` witness.
For arbitrary models `X` and `Y` over `Spec R` and a morphism `f` over
that base, assume that `f.left` is quasi-compact and quasi-separated
and that `X.hom` is quasi-compact. Its actual `baseChangeMap` to the
colimit ring is separated if and only if its actual counterpart over
some stage algebra is separated. The scheme-limit witness is constructed
from the algebra-colimit witness by `spectrumConeIsLimit`.

`InitialRingSeparatednessDescent` starts with the original ring functor
`F`, its actual colimit cocone `c` and chosen initial object `j₀`.
With the same relative hypotheses, separatedness along exactly
`Spec.map (c.ι.app j₀)` is equivalent to separatedness along exactly
`Spec.map (F.map j.hom)` for some `j : Under j₀`.
The eventual stage contains an actual arrow from the original initial
stage. The constructed `initialRingAlgebraDiagram` retains these rings
and maps and `initialRingAlgebraCoconeIsColimit` derives its colimit
witness. Its spectrum maps are the maps displayed in the proposition.
For a directed poset, this gives a stage greater than or equal to `j₀`.

`FinitePresentationInitialRingSeparatednessDescent` gives the source
specialization: both model structure maps are locally of finite
presentation, quasi-compact and quasi-separated. These conditions are
Conrad's finite-presentation convention, including over nonnoetherian
rings. Quasi-compactness of the source structure map together with
quasi-separatedness of the target structure map implies
quasi-compactness of `f.left`; quasi-separatedness of the source
structure map implies quasi-separatedness of `f.left`. These relative
conditions are derived, rather than added as assumptions on `f`.

The first two forms are derived strengthenings of the source clause;
they do not require local finite presentation. The third states the
source separatedness clause for the original filtered ring system.
All forms retain arbitrary nonaffine and nonseparated models and
noninjective transition maps. The paired Lean file defines propositions
only. The proof specializes `RelativeSeparatednessDescent` to the actual
spectrum diagram and then the constructed original initial-stage tail.
Other source properties remain separate obligations.
