# Existence of local algebra approximation systems (Stacks 00QV), proof

The closing theorem is `Langlands.Algebra.localAlgebraApproximationExistence.{uR, uS}`. Its
complete type is the published proposition
`Langlands.Algebra.LocalAlgebraApproximationExistenceStatement.{uR, uS}` (Stacks, Tag 00QV,
Lemma 10.127.11), with independent ambient universes `uR` and `uS`. It has no further
hypotheses. The final unapplied-constant `example` checks this type directly. The statement
pair and its imports are unchanged.

## Implemented proof

Fix local rings `R : Type uR` and `S : Type uS`, a local algebra map `R → S`, and
`hS : EssFinitePresentation R S`. The proof applies
`LocalAlgebraApproximationExistence.exists_isApproximation R S hS`
(module `Langlands.Algebra.LocalAlgebraApproximationExistence`). It does the following:

- it chooses a presentation `P : Pres (ULift.{uS} R) R S ULift.ringEquiv` of `S`;
- it builds the system `P.system`, indexed by `Finset (ULift.{uS} R)`, whose base rings are
  local subrings of `ULift R` essentially of finite type over `ℤ` and whose algebras are
  localizations of finite type quotients of polynomial rings at the inverse images of the
  maximal ideal of `S`;
- it proves the colimit clause and both essential-finite-type clauses of
  `LocalAlgebraSystem.IsApproximation`.

The index type and every component ring live in `Type (max uR uS)`. The carriers `R` and `S`
of the system are the given rings.

The remaining prime-localization clause is supplied for every presentation and every `i ≤ j`
by `LocalAlgebraApproximationExistence.Pres.isPrimeLocalization_system`
(module `Langlands.Algebra.LocalAlgebraApproximationTransition`). That theorem uses the actual
`ringBaseChangeMap` of the system and exactly its induced algebra structure.
