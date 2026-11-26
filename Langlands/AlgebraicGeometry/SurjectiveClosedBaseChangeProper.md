# Properness reflected along a surjective closed immersion of the base

Module `Langlands.AlgebraicGeometry.SurjectiveClosedBaseChangeProper`, namespace
`Langlands.AlgebraicGeometry.SurjectiveClosedBaseChange`.

Let `p : X ⟶ S` and `t : T ⟶ S` be morphisms of schemes. The typical case is a nilpotent
thickening `t`, such as `Spec R ⟶ Spec R'` for a surjection of rings with nilpotent
kernel.

## Declarations

- `squareMap p t`: the canonical morphism from the fibre square of
  `pullback.snd p t` (over `T`) to the fibre square of `p` (over `S`), induced by
  `pullback.fst p t` on both factors.
- `isPullback_squareMap`: this morphism is the base change of `t` along the structure map
  of the fibre square of `p`. The proof checks the universal property directly.

Assume now `[IsClosedImmersion t]` and `[Surjective t]`.

- `universallyClosed`: if `pullback.snd p t` is universally closed, so is `p`. The
  composite `pullback.fst p t ≫ p = pullback.snd p t ≫ t` is universally closed and
  `pullback.fst p t` is surjective, so Mathlib's `UniversallyClosed.of_comp_surjective`
  applies.
- `isSeparated`: if `pullback.snd p t` is separated, so is `p`. The diagonal of `p` is an
  immersion. Its image equals the image under `squareMap p t` of the (closed) image of the
  diagonal of `pullback.snd p t`, because `pullback.fst p t` is surjective and
  `pullback.fst p t ≫ diagonal p = diagonal (pullback.snd p t) ≫ squareMap p t`.
  `squareMap p t` is a closed immersion, being a base change of `t`. Hence the diagonal has
  closed image and is a closed immersion (Mathlib's `IsClosedImmersion.of_isPreimmersion`).
- `isProper`: if `pullback.snd p t` is proper and `p` is locally of finite type, then `p`
  is proper.

## Provenance

Internal derived content: these are the standard topological arguments that separatedness
and universal closedness can be checked after a surjective closed immersion of the base,
proved here from Mathlib's definitions. They are used to show that a lift of a proper
scheme across a nilpotent thickening is proper.
