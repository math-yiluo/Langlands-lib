# Relative smoothness and flatness over the original filtered ring system

This unit records the smooth and flat clauses of Brian Conrad, *Weil and
Grothendieck approaches to adelic points* (December 31, 2011), printed
pp. 5–6, Theorem 3.4(2), for the actual initial ring, colimit and transition
maps. Registered source `conrad-2011-weil-grothendieck-adelic-points`,
SHA-256 `fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
All sizes share arbitrary universe `u`.

`RingSystemRelativeSmoothFlatDescent` conjoins three forms, each of which
conjoins the smooth and flat equivalences. The stages witnessing the two
properties may differ. The property-parameterized definitions only specify
the forms; the aggregate asserts them for these two concrete properties.

`SpectrumRelativePropertyDescent` uses an actual small filtered diagram of
commutative `R`-algebras and its actual colimit cocone. For arbitrary models
`X` and `Y` over `Spec R` and a morphism `f : X ⟶ Y`, assume `f.left` is
locally of finite presentation, quasi-compact and quasi-separated, and
`Y.hom` is quasi-compact. Its actual `baseChangeMap` over the cocone ring
has the property if and only if it has the property over some original
algebra stage. The scheme-limit comparison is constructed by
`spectrumConeIsLimit`, rather than assumed.

`InitialRingRelativePropertyDescent` uses the original ring functor `F`,
colimit cocone `c`, and chosen initial stage `j₀`. With the same relative
finiteness hypotheses, the property along exactly
`Spec.map (c.ι.app j₀)` is equivalent to the property along exactly
`Spec.map (F.map j.hom)` for some `j : Under j₀`. This retains an actual
arrow from the original initial stage. The published initial-stage algebra
tail and its proved colimit witness realize these exact maps. For a
directed poset, this is precisely a stage greater than or equal to `j₀`.

`FinitePresentationInitialRingRelativePropertyDescent` gives the source
specialization: both model structure maps are locally of finite
presentation, quasi-compact and quasi-separated. This is Conrad's
finite-presentation convention, including over nonnoetherian rings.
These model hypotheses imply all the relative hypotheses on `f`.
The published `Langlands.AlgebraicGeometry.locallyOfFinitePresentation_of_comp`
derives local finite presentation of `f.left` from that of its composite
with `Y.hom` and local finite type of `Y.hom`. Quasi-compactness follows
from quasi-compactness of the source structure map and quasi-separatedness
of the target structure map. Quasi-separatedness follows from that of the
source structure map. No extra relative hypothesis is assumed.

The first two forms are derived strengthenings with arbitrary small
filtered categories and the stated weaker relative hypotheses. The third
is the source clause for prescribed finitely presented models. Every form
allows arbitrary nonaffine and nonseparated models and noninjective ring
transitions, with no noetherian, arithmetic or topological hypotheses.
The Lean file defines propositions only. The proof specializes
`RelativeSmoothFlatDescent` to spectra and the actual initial-stage algebra
tail, and then derives the relative hypotheses from finite presentation
of the models. The other clauses of Theorem 3.4(2) remain separate.
