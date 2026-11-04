# Open-immersion descent over the original filtered ring system

This statement isolates the open-immersion clause of Brian Conrad,
*Weil and Grothendieck approaches to adelic points* (December 31, 2011),
printed pp. 5–6, Theorem 3.4(2). The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
All sizes share arbitrary universe u.

`RingSystemOpenImmersionDescent` conjoins three forms.
`SpectrumOpenImmersionDescent` uses an actual small filtered diagram of
commutative R-algebras, an actual cocone and its `IsColimit` witness.
For models X and Y over Spec R and a morphism f over that base, assume
local finite presentation and quasi-compactness of X.hom, and local finite
presentation and quasi-separatedness of Y.hom. The actual `baseChangeMap`
to the colimit ring is an open immersion if and only if its actual
counterpart over some stage algebra is an open immersion. The required
scheme-limit witness is constructed by `spectrumConeIsLimit`.

`InitialRingOpenImmersionDescent` starts with the original ring functor F,
its actual colimit cocone c and an arbitrary chosen initial stage j₀.
With the same hypotheses on the two structure maps, open immersion along
exactly `Spec.map (c.ι.app j₀)` is equivalent to open immersion along
exactly `Spec.map (F.map j.hom)` for some `j : Under j₀`. Thus the eventual
stage carries an actual arrow from the original chosen stage, and both
base changes use the original ring maps. The constructed
`initialRingAlgebraDiagram` retains these rings and maps, and
`initialRingAlgebraCoconeIsColimit` derives its colimit witness from the
original cocone. For a directed poset, the conclusion is a stage greater
than or equal to j₀.

These first two forms are derived strengthenings of the source clause.
In the relative open-image proof, compactness of the limiting source
requires quasi-compactness of X.hom. Local finite presentation of X.hom
factors the inverse and descends its left identity. Local finite
presentation of Y.hom descends its right identity; quasi-separatedness
of Y.hom makes the target open diagram quasi-separated. That argument
uses neither quasi-separatedness of X.hom nor quasi-compactness of Y.hom.
The exported helper `exists_isOpenImmersion_baseChangeMap` retains
precisely these weaker hypotheses, while base-change stability proves
the reverse implication without further finiteness hypotheses.

`FinitePresentationInitialRingOpenImmersionDescent` is the original source
form: both model structure maps are locally of finite presentation,
quasi-compact and quasi-separated, exactly Conrad's finite-presentation
convention even over nonnoetherian rings. It specializes the second form
without additional hypotheses on the relative morphism.

All forms retain arbitrary nonaffine and nonseparated models and
noninjective transition maps. The paired Lean file defines propositions
only. Proofs and the other source-property clauses remain separate
obligations.
