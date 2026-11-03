# Assembling projectivity from local splitness on smooth localizations

This module combines the steps of the proof of
`Langlands.CommutativeAlgebra.IntegralFibreProjectivityStatement` (Stacks Project, Tag 05FT).
One local input stays a hypothesis here: local splitness of `S_s ⊗[R] S` over each smooth
localization `S_s` with free differentials. Given that input, it proves that `S` is projective.

## Statement

- `Langlands.CommutativeAlgebra.projective_of_forall_locallySplit_away`: let `R` and `S` be
  commutative rings in one universe `u` and `S` a flat finitely presented `R`-algebra.
  Assume:
  - `K ⊗[R] S` is a domain for every field `K : Type u` with an `R`-algebra structure;
  - for every `s : S` such that `Localization.Away s` is smooth over `R` (`Algebra.Smooth`) and
    `Ω[Localization.Away s⁄R]` is free over `Localization.Away s`, the module
    `Localization.Away s ⊗[R] S` is locally split over `Localization.Away s`
    (`Langlands.CommutativeAlgebra.LocallySplit`).

  Then `S` is a projective `R`-module (`Module.Projective R S`).

## Proof

`Langlands.CommutativeAlgebra.exists_smooth_free_cover` gives `s : Fin m → S` such that every
`S_{s i}` is smooth over `R` with free differentials, and `R' = ∀ i, S_{s i}` is faithfully flat
over `R`. By the second hypothesis, `S_{s i} ⊗[R] S` is locally split over `S_{s i}` for every
`i`. So `Langlands.CommutativeAlgebra.locallySplit_pi` makes `R' ⊗[R] S` locally split over `R'`.
`S` is flat over `R`, and countably generated as an `R`-module by
`Langlands.CommutativeAlgebra.exists_countable_span_eq_top`. Hence
`Langlands.CommutativeAlgebra.projective_of_locallySplit_baseChange` shows that `S` is
projective.

## Provenance

The decomposition follows Worker 281's route to Tag 05FT: cover by smooth localizations, local
splitness on each factor, then descent of projectivity. It replaces the Stacks Project route
through Noetherian approximation and Tag 05FS. Worker 928 wrote this module. The module is
internal to the project.
