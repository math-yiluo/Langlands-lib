# Injectivity preservation by Renard's actual I functor

`Langlands.Algebra.nondegenerateIInductionInjectivity` proves exactly the
published closed proposition
`Langlands.Algebra.NondegenerateIInductionInjectivityTheorem.{uA,uB,v}`.
For every nondegenerate A-module X at carrier universe `w = max uB v`, it
proves both source exact-Hom injectivity and Mathlib injectivity of the actual
`RenardHomFunctors.I.obj X` from the corresponding injectivity of X.

The theorem retains the specified left A-action on B, the named right regular
B-action, their commutation and the source nondegenerate A–B bimodule
hypothesis. It installs exactly `NondegenerateModuleCat.abelian` for A and B
at w. Both actual functors are specialized to source carrier w; their target
carrier universe `max uB w` is definitionally w. The ring universes uA and uB
remain independent, including when uA is larger than w.

The proof imports `nondegenerateFInductionExactness` at universes
`uA, uB, w`, and takes its `SequenceExact F` component. It also imports
`NondegenerateInductionAdjunction.nondegenerateFInductionAdjunction` at
`uA, uB, v`. The first witness of its canonical-adjunction conclusion is an
actual adjunction between precisely this F and I. Neither result is an extra
premise of the injectivity theorem.

The private categorical helper applies the left-exact part of `SequenceExact`
to short exact complexes. Mathlib's
`Functor.preservesMonomorphisms_of_preserves_shortExact_left` then gives
preservation of monomorphisms by F. For the actual adjunction,
`CategoryTheory.Adjunction.map_injective` proves that I preserves the Mathlib
injective extension property. Finally,
`Langlands.Renard.homInjectiveComparison` converts source exact-Hom
injectivity of X to this extension property and converts the conclusion back.
Here `HomInjective` uses the actual contravariant integer-module-valued Hom
functor. Thus both required conclusions concern the same actual I-object.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`: I.2.4, printed
pp.18–19 / PDF24–25, with the injectivity corollary on printed p.19 / PDF25.
The conventions and constructions are on printed pp.5–7 / PDF11–13 and
pp.15–18 / PDF21–24; the exactness and injectivity definitions A.VIII.1–2
are on printed pp.266–267 / PDF272–273. The registered supplementary
`renard-2010-corrections-complements`, PDF1–2 and PDF18–19, includes the
corrected direction F left adjoint to I, consistent with the 2026 edition.

The implementation uses the injective extension property along the actual
adjunction; Renard presents the corollary through composition of exact Hom
functors. This arbitrary nonunital-ring additive formulation is the internal
one already fixed by the published proposition. Complex coefficient actions,
complex-linearity, scalar restriction and comparison with unitization remain
separate obligations. This theorem proves the injectivity corollary only.
