# Relative affineness over the actual filtered ring system

This statement isolates the affineness clause of Brian Conrad, *Weil and
Grothendieck approaches to adelic points* (December 31, 2011), printed
pp. 5–6, Theorem 3.4(2), with its actual initial coefficient ring and
subsequent ring maps. `RingSystemAffinenessDescent` is the conjunction
of three precise forms of that assertion, in an arbitrary common
universe `u`.

`SpectrumAffinenessDescent` starts with a small filtered diagram of
commutative `R`-algebras, an actual cocone `c`, and its `IsColimit`
witness. The models `X` and `Y` are arbitrary schemes over `Spec R`,
and `f` is a morphism over that base. Assume only that `f.left` is
quasi-compact and quasi-separated and that `Y.hom` is quasi-compact.
The actual pullback-induced morphism `baseChangeMap` over the cocone
ring is affine if and only if its base change to one stage algebra
is affine. The maps used here are the published `spectrumBaseMap` and
`spectrumStructure`; the scheme-limit universal property is supplied
by `spectrumConeIsLimit` from the algebra-colimit witness.

`InitialRingAffinenessDescent` instead starts with an original functor
`F : J ⥤ CommRingCat`, an actual colimit cocone `c`, and a chosen
stage `j₀`. Its models are over the actual spectrum of `F.obj j₀`.
With the same relative qcqs and target quasi-compactness assumptions,
affineness after base change along `Spec.map (c.ι.app j₀)` is equivalent
to affineness along `Spec.map (F.map j.hom)` for some `j : Under j₀`.
Thus the eventual stage includes an actual arrow from the chosen
stage. No algebra-tail colimit identification is an extra premise:
`initialRingAlgebraCoconeIsColimit` constructs it from the original
ring-colimit witness, and the proved spectrum formulas identify the
structural maps with exactly the maps displayed in this statement.
For a directed poset, the objects of `Under j₀` are precisely its
stages greater than or equal to `j₀`, with their given transitions.

`FinitePresentationInitialRingAffinenessDescent` states the original
source's finiteness specialization explicitly. Both model structure
maps are locally of finite presentation, quasi-compact and
quasi-separated. These three conditions are the source's definition
of finite presentation over a ring, also over nonnoetherian rings.
They imply the relative hypotheses in the preceding form: quasi-
separatedness of the source structure map implies that of `f`, and
quasi-compactness of the source structure map together with quasi-
separatedness of the target structure map implies quasi-compactness
of `f`. These are implications to be used in the proof, not additional
assumed properties of `f`.

The first two forms are derived strengthenings of Conrad's assertion:
they permit small filtered categories and the weaker stated relative
finiteness conditions. All three retain nonaffine and nonseparated
models and arbitrary, possibly noninjective, ring transitions. There
are no arithmetic, noetherianity or topology assumptions.

This pair defines propositions only. The proof is a separate unit,
obtained by specializing `RelativeAffinenessDescent` to the actual
spectrum diagram and then to the constructed initial-stage algebra
tail. Other properties of Theorem 3.4(2), Hom and prescribed-isomorphism
descent, initial-model existence and point topologies remain separate
obligations.
