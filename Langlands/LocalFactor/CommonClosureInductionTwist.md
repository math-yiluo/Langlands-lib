# Twisting, trivial induction and the common-closure generator span

Helper module for the proof of
`Langlands.LocalFactor.CommonClosureDegreeZeroGenerationStatement`
(Tate, *Number theoretic background*, Corvallis 1979, proof of (2.3.1),
printed page 11). Tate's argument uses two elementary facts about induction:
the projection formula `χ ⊗ Ind V ≅ Ind (Res χ ⊗ V)` and the trivial
case `Ind_E^E V = V`. The projection formula on the actual induced spaces is the
Library equivalence `FiniteRepresentation.induceTwistEquiv`
(module `Langlands.VirtualRepresentation.ExactInductionTwist`). This module
transports it to common-closure induction, proves the trivial case on the
actual models used by the target, and derives the two span facts the final
assembly needs.

## Generic finite-index induction (`Langlands.FiniteRepresentation`)

The project's induction `FiniteRepresentation.induce S A` is Mathlib's
coinduced space `Representation.coindV S.subtype A.representation` of
functions `f : G → V` with `f (s * g) = A s (f g)`, with `G` acting by right
translation.

- `induceTopLinearEquiv hS φ hφ A` and `induceTopEquiv hS φ hφ A`: if every
  element of `G` lies in `S` (`hS`), and `φ : S →* G` sends each `s` to its
  underlying element (`hφ`), then evaluation at `1` is an intertwining
  equivalence `induce S (restrict φ A) ≅ A`. Its inverse sends `a` to
  `x ↦ A x a`.

## Actual common-closure groups (`Langlands.LocalFactor.CommonClosure`)

- `weilInclusion F E L h`: for `E.field ≤ L.field`, the continuous inclusion
  `weilSubgroup F L →ₜ* weilSubgroup F E` of the actual Weil subgroups.
- `continuousTwist_induce F E L h χ x`: for a continuous character
  `χ : weilSubgroup F E →ₜ* ℂˣ` and `x : Virtual F L`,
  `continuousTwist χ (induce F E L h x) =
    induce F E L h (continuousTwist (χ.comp (weilInclusion F E L h)) x)`.
  Both sides are `ℤ`-linear in `x`, so by `ExactGrothendieckGroup.hom_ext` it
  suffices to check genuine representation classes. There it is
  `induceTwistEquiv` applied to the rebracketed restriction used by
  `CommonClosure.induce`. Restricting along `nestedWeilEquiv` commutes with
  twisting definitionally.
- `induce_self F E h`: `induce F E E h = LinearMap.id`. On generators it is
  `induceTopEquiv`, because every element of `weilSubgroup F E` lies in the
  rebracketed subgroup, and `nestedWeilEquiv F E E h` sends each element to
  its underlying element.

## Span facts (`Langlands.LocalFactor`)

Write `S(E)` for `Submodule.span ℤ (characterDifferenceInductionGenerators F E)`.

- `characterClass_sub_mem_span F E χ χ'`: for continuous characters
  `χ χ'` of `weilSubgroup F E`, the difference
  `characterClass χ - characterClass χ'` lies in `S(E)`. It is the generator
  with `L = E`, by `induce_self`.
- `continuousTwist_mem_span F E χ hx`: if `x ∈ S(E)`, then
  `continuousTwist χ x ∈ S(E)`. By `continuousTwist_induce` and
  `continuousTwist_characterClass`, the twist of the generator
  `induce F E L h (characterClass ψ - characterClass ψ')` is the generator
  `induce F E L h (characterClass (χ|_L * ψ) - characterClass (χ|_L * ψ'))`,
  where `χ|_L = χ.comp (weilInclusion F E L h)`.
