# Group actions on étale cohomology with constant coefficients

Author: Worker 13. Built on Worker 13's `Langlands.Geometry.EtaleCohomologyAction`
and `Langlands.Cohomology.TranslationCoaction`, Worker 13's published
`Langlands.Geometry.EtaleDerivedSections`, and Mathlib's constant sheaves.

Let `Y : Scheme.{u}`, `R : Type u` a commutative ring, `G` a group, and
`ρ : G →* (Aut Y)ᵐᵒᵖ`, with the translation data `data R ρ` of
`EtaleCohomologyAction`.

## Definitions

- `constant R M` is Mathlib's constant étale sheaf of an `R`-module `M`, the
  sheafification of the constant presheaf.
- `constantAdj R` is Mathlib's adjunction `constantSheafAdj` between constant
  sheaves and sections over the terminal object of `Y.Etale`.
- `constantCoact R ρ M g : constant R M ⟶ translate (constant R M)` is the
  morphism that `constantAdj` assigns to the unit at `M` followed by the
  inverse of `(data R ρ).sections g`. It is characterized by
  `unit_comp_map_constantCoact`: the unit followed by sections of
  `constantCoact` is the unit followed by that inverse.
- `constantCoequivariant R ρ M` is the constant sheaf with these structure
  maps, an object of `TranslationAction.Coequivariant (data R ρ)`. Both
  cocycle conditions are checked after the adjunction's bijection. They follow
  from `unit_comp_map_constantCoact`, naturality of the section isomorphisms,
  and `TranslationAction.sections_comp_inv` and `sections_one_inv`.
- `constantCohomologyRep R ρ M n : Rep R G` is Mathlib's `Rep.ActionToRep`
  of `TranslationAction.coCohomologyAction` for Mathlib's chosen injective
  resolution of `constant R M`.
- `constantCohomologyIso R ρ M n` identifies the underlying module with the
  published `EtaleDerivedSections.constantCohomology Y R n` at `M`.

## Provenance and scope

Harris, *Galois properties of cohomological automorphic forms on GL(n)*, J.
Math. Kyoto Univ. 39-2 (1999), Theorem 5.7, printed p.313, considers Galois
actions on étale cohomology of Shimura varieties. Worker 13 read this passage
in the original. The coefficients there are the systems of the paper's
section 3. Here the coefficients are constant, and the group action is given.
This is derived infrastructure. Not treated here: locally constant or
descended coefficient sheaves, comparison with a definition by inverse images,
continuity, and compact supports.

Source registration:
Harris, `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Project imports outside this submission are present in Library commit
`0686b4fa6c8df22845bba2e2668a723a41d47c84`.
