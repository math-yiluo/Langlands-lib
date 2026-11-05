# Finite coefficient models of finitely generated tensor ideals

Worker 105. This internal construction implements the finite-coefficient step
in the proof of Stacks Project Lemma 33.8.15 (04KZ). It uses the existing Library
single-tensor finite-stage lemma in `DVRAlgebraicBaseChange`; none of its DVR
hypotheses are present on that lemma or on this construction.

For an arbitrary algebraic field extension `L/K`, a commutative `K`-algebra `A`,
and a finite indexed family of finitely generated ideals in `L ⊗[K] A`,
`FiniteTensorIdealModel.construct` chooses one actual intermediate field `E`
finite dimensional over `K` and finitely generated ideals in `E ⊗[K] A`.
Their extensions under the actual tensor map induced by `E → L` equal the
original ideals. No finiteness, reducedness or domain assumption is placed
on `A`. The base field, extension field, algebra and index type have independent
universes `u`, `v`, `w`, `z`.

The imported `DVRAlgebraicBaseChange.stageMap` is the Library's tensor map
of the intermediate-field inclusion and the identity of `A`. Finite induction combines the existing
single-element finite stages by their supremum, whose degree is finite.
The proof then takes a finite generating set for every ideal and applies
that result to their finite union. Lift those generators to the common stage
and take the ideals they generate. `Ideal.map_span` proves the exact extension
identities; their finite generation follows directly from their finite sets of
generators. The more general helper `exists_fg_ideal_map_eq_span` implements
this last step for any semiring homomorphism containing a finite
set in its range.

Original source: registered `stacks-finite-coefficient-descent-04KZ-2026-11-04`,
SHA256 `9f5bd264065a4948acc0c96e0c72e7431d4d6c288a925989c05802ee76c3a15b`,
retained `Stacks Project - Components defined over finite extensions
(tag 04KZ, HTML snapshot 2026-11-04).html`, Lemma 33.8.15, proof's first
paragraph from the choice of the finitely generated prime ideal through the
choice of a finite subextension containing all generator coefficients.
The finite-family and arbitrary-`A` packaging here is a derived algebraic
construction. The source's component descent additionally uses Galois
invariance and other geometric arguments. This unit constructs no component
scheme and proves neither full 04KZ nor finite separable component splitting
054R. It does not assert separability of `E/K` for an arbitrary algebraic `L/K`.
The retained lemma page has no comments; no applicable project errata file
was present when checked.
