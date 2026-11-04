# Finite-morphism descent over the original filtered ring system

This statement isolates the finite-morphism clause of Brian Conrad,
*Weil and Grothendieck approaches to adelic points* (December 31, 2011),
printed pp. 5–6, Theorem 3.4(2), using the actual original initial ring
and its given transition maps. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
All sizes share arbitrary universe `u`.

`RingSystemFiniteDescent` conjoins three precise forms.
`SpectrumFiniteDescent` uses an actual small filtered diagram
of commutative `R`-algebras, an actual cocone and its `IsColimit` witness.
For arbitrary models over `Spec R` and a morphism `f` over that base,
assume `f.left` is locally of finite type, quasi-compact and
quasi-separated, and the target structure map is quasi-compact.
The actual `baseChangeMap` over the cocone ring is finite
if and only if it is finite over some stage algebra.
`spectrumConeIsLimit` constructs the scheme-limit witness from the
algebra-colimit witness; it is not an additional assumed comparison.

`InitialRingFiniteDescent` starts with the original ring
functor `F`, an actual colimit cocone `c` and a chosen initial stage
`j₀`. With the same relative finiteness hypotheses, finiteness
along exactly `Spec.map (c.ι.app j₀)` is equivalent to finiteness
along exactly `Spec.map (F.map j.hom)` for some `j : Under j₀`.
The eventual stage thus includes an actual arrow from the original
initial stage. The published `initialRingAlgebraDiagram` retains the
original rings and maps; `initialRingAlgebraCoconeIsColimit` derives its
algebra-colimit witness. The spectrum-map formulas identify these maps
with the ones displayed in the proposition. For directed posets this
is precisely an eventual stage greater than or equal to `j₀`.

`FinitePresentationInitialRingFiniteDescent` gives the source
specialization: both model structure maps are locally of finite
presentation, quasi-compact and quasi-separated. These three conditions
express Conrad's finite-presentation convention, including over
nonnoetherian rings. They imply the hypotheses on `f`: local finite
type follows from that of the composite structure map; quasi-compactness
follows from that of the source structure map and quasi-separatedness
of the target structure map; quasi-separatedness follows from that of
the source structure map. The statement adds none of these as further
assumptions on `f`.

The first two forms are derived strengthenings, permitting arbitrary
small filtered categories and the stated weaker relative finiteness
conditions. The third records the source clause for the actual original
ring system. Every form retains arbitrary nonaffine and nonseparated
models and noninjective transitions, and imposes no arithmetic or
topological hypotheses. The paired Lean file defines propositions only.
The proof specializes `RelativeFiniteDescent` to the actual
spectrum diagram and then the constructed initial-stage algebra tail.
The other properties of Theorem 3.4(2) remain separate obligations.
