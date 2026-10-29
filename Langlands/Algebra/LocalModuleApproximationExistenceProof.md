# Existence of local module approximation systems (Stacks 00QX), proof

The closing theorem is `Langlands.Algebra.localModuleApproximationExistence.{uR, uS, uM}`.
Its complete type is the published proposition
`Langlands.Algebra.LocalModuleApproximationExistenceStatement.{uR, uS, uM}` (Stacks Project,
Lemma 10.127.13, tag [00QX](https://stacks.math.columbia.edu/tag/00QX)). The three ambient
universes `uR`, `uS` and `uM` stay independent. The theorem has no further hypotheses. The
final unapplied-constant `example` checks this type directly. Neither the statement pair nor
any module it imports is edited.

## Implemented proof

The proof is a single term that combines two published results:

```lean
localModuleApproximationExistence_of_localAlgebraApproximationExistence
  localAlgebraApproximationExistence.{uR, max uS uM}
```

- `Langlands.Algebra.localAlgebraApproximationExistence.{uR, max uS uM}`
  (module `Langlands.Algebra.LocalAlgebraApproximationExistenceProof`) is the published
  proof of Stacks 00QV, `LocalAlgebraApproximationExistenceStatement`, here instantiated at
  the universes `uR` and `max uS uM`. That proof builds its ring systems from localizations of
  finite type quotients of polynomial rings at the inverse images of the maximal ideal (see
  its Markdown). The present proof uses only the published proposition, so it depends on that
  construction only through the existential statement.
- `Langlands.Algebra.localModuleApproximationExistence_of_localAlgebraApproximationExistence`
  (module `Langlands.Algebra.LocalModuleApproximationReduction`) has the type
  `LocalAlgebraApproximationExistenceStatement.{uR, max uS uM} →
  LocalModuleApproximationExistenceStatement.{uR, uS, uM}`.

For a local map `R → S` with `EssFinitePresentation R S` and a finitely presented `S`-module
`M`, the reduction proceeds in four steps. The details are in the reduction module's Markdown.

1. **Universe transport.** It applies 00QV to `R → ULift.{uM} S`. That ring is local, its
   structure map is local, and it is essentially finitely presented over `R`, by transport
   along `ULift.algEquiv`. So the index and all component rings lie in `max uR uS uM`, as
   00QX requires. The cocone is then transported back to `S` along `ULift.algEquiv` with
   `LocalAlgebraSystem.mapAlgEquiv`. The theorem
   `LocalAlgebraSystem.mapAlgEquiv_isApproximation` proves that the transported ring system
   is still an approximation system. This is the compatibility of
   the transport.
2. **Matrix presentation.** It obtains a matrix `A : Matrix (Fin n) (Fin m) S` and an
   equivalence `(Fin n → S) ⧸ range A.mulVecLin ≃ₗ[S] M`, using `exists_matrix_presentation`.
3. **Lifting.** It lifts the finitely many entries of `A` to one component `i₀` of the ring
   system, using `LocalAlgebraSystem.exists_algι_eq_fun`.
4. **Cokernel system.** It takes the tail of the ring system above `i₀` and the presentation
   system `Coker(A_λ)` on it (`LocalAlgebraSystem.presentationSystem`). The theorem
   `presentationSystem_isApproximation` proves that this system is an approximation system.
   The system is then transported to `M` along the presentation equivalence
   (`LocalModuleSystem.mapLinearEquiv`, preserved by
   `LocalModuleSystem.mapLinearEquiv_isApproximation`).

The witnesses are therefore one ring system and one module system over it, constructed
jointly. The ring system is a tail of a 00QV system, not an arbitrary preselected one.
`LocalModuleSystem.IsApproximation` is the published predicate, with all six conditions on
the actual canonical maps:

- both ring direct limits;
- the additive module direct limit;
- the finite-type conditions on the components;
- module finiteness at each stage;
- prime localization through `ringBaseChangeMap.toAlgebra`;
- bijectivity of the scalar-first `moduleBaseChangeMap`.

## Provenance

This is the Stacks proof of Lemma 10.127.13 (00QX). Choose a ring system by Lemma 10.127.11
(00QV), lift a presentation matrix of `M` to some `S_λ₂`, and set `M_λ = Coker(A_λ)` for
`λ ≥ λ₂`. The verification that Stacks leaves to the reader is the published
`presentationSystem_isApproximation`. The `ULift` transport is internal size packaging: the
published 00QV statement places its witnesses in the maximum of two universes, while 00QX
needs the maximum of three.
