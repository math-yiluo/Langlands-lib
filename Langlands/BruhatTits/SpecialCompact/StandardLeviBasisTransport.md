# Compact-open normal bases on the actual standard Levi schemes

Module `Langlands.BruhatTits.SpecialCompact.StandardLeviBasisTransport`, namespace
`Langlands.BruhatTits.SpecialCompact`.

## Purpose and provenance

`SimultaneousStandardBasisAt i ν K0` (module `StandardBasisProperty`) asks for one set `B` of
subgroups of `G(F)` with three properties:

- `B` is a compact-open normal basis relative to `K0`;
- for every `J ⊆ Δ`, the literal intersections of `B` with `M_J(F)` form an inherited
  compact-open normal basis;
- for every `J ⊆ Δ`, `B` satisfies the Iwahori and contraction clauses for a compatible split
  component.

A rank induction over standard Levis needs the same property for the actual Levi scheme
`L = Standard.leviScheme i ν J`. On `L` the torus is `Standard.leviTorusHom i ν J` and the compact
subgroup is `leviSchemeCompact K0 i ν J = j⁻¹(K0)`, where `j = Standard.leviHom i ν J`. The
docstring of `leviSchemeCompact` in the Library cites Waldspurger I.1 (J. Inst. Math. Jussieu 2
(2003)) for the principle that `M ∩ K` has, relative to `M`, the properties that `K` has relative
to `G`.

This module proves the first two properties for `L`. The basis it uses is the set of literal
preimages `leviSchemeBasis i ν J B = {j⁻¹(K) | K ∈ B}`. Its members are exactly
`leviSchemeCompact K i ν J` for `K ∈ B`, the subgroups at which the companion transports of the
Iwahori and contraction clauses are stated. The third property and the assembly of the full
`SimultaneousStandardBasisAt` on `L` are not part of this module.

Provenance is **derived**. No statement is quoted from a source. Every result is a short
corollary of published Library results: the definitions in `SmallSubgroupPredicates` and
`StandardBasisProperty`, the Levi-scheme points identification `leviSchemePointsEquiv`
(`RationalLeviScheme`), `standardLeviStandardFamilies` (intrinsic standard families of `L` are
the preimages of the ambient ones), `standardLevi_mono_of_exists` and `standardCocharacter`.
The module introduces only the preimage family `comapFamily`, its Levi-scheme instance
`leviSchemeBasis`, and one topological-group identification.

## Conventions

- `F` is a nonarchimedean local field. `G` is an affine group scheme over `Spec F`, locally of
  finite type.
- `i` is a maximal split torus, `ν` a generic cocharacter and `Δ = simpleRelativeRoots i ν`.
- For `J ⊆ Δ`, `L = Standard.leviScheme i ν J` with closed immersion `j = Standard.leviHom i ν J`,
  and `iL = Standard.leviTorusHom i ν J`.
- Rational points carry the Library's identity-test topology `rationalPointTopology`. This is the
  topology that `SimultaneousStandardBasisAt` fixes with `letI`. The module uses the Library's
  local instances `rationalWeightsTopology` and `leviScheme_isAffineHom`, which agree with it
  definitionally.

## Group-level transport

Let `H`, `G` be groups and `f : H →* G`.

- `comapFamily f B`: the set of literal preimages `K.comap f`, `K ∈ B` (`mem_comapFamily`).
- `intersectionFamily_eq_comapFamily`: the inherited family `intersectionFamily M B` is
  `comapFamily M.subtype B`.
- `comapFamily_comapFamily`: preimage families compose, so
  `comapFamily g (comapFamily f B) = comapFamily (f ∘ g) B`.

Now let `H`, `G` carry topologies and let `e : H ≃ₜ* G` be an isomorphism of groups that is
also a homeomorphism.

- `CompactOpenNormalBasis.comap_continuousMulEquiv`: if `B` is a compact-open normal basis
  relative to `K0`, then `comapFamily e B` is one relative to `e⁻¹(K0)`. Inclusion, normality in
  `K0`, openness and compactness each pass to preimages. The neighbourhood filter of `1` in `H`
  is the pullback of that of `1` in `G`.

## The Levi scheme

- `leviSchemeBasis i ν J B := comapFamily (rationalPoints.map j) B`. By `mem_leviSchemeBasis`,
  its members are exactly `leviSchemeCompact K i ν J` with `K ∈ B`.
- `compactOpenNormalBasis_leviScheme`: assume `InheritedCompactOpenNormalBasis K0 M_J(F) B`.
  Then `leviSchemeBasis i ν J B` is a compact-open normal basis of `L(F)` relative to
  `leviSchemeCompact K0 i ν J`. The proof transports along `leviSchemePointsEquiv : L(F) ≃ₜ* M_J(F)`,
  whose composite with the inclusion `M_J(F) → G(F)` is `rationalPoints.map j`. No structural
  hypothesis on `G` is needed.

From here on `G` is connected reductive, `i` is maximal split, `ν` is generic and `J ⊆ Δ`.
Let `R ⊆ J`.

- `mem_standardLeviPoints_leviTorusHom_iff`: a point `x` of `L(F)` lies in
  `standardLeviPoints iL ν R` if and only if `j(x)` lies in `M_R(F) = standardLeviPoints i ν R`.
  This is the `standardLevi` clause of `standardLeviStandardFamilies`.
- `simpleRelativeRoots_leviTorusHom_eq`: the simple roots of `iL` are exactly `J`.
- `standardLeviPoints_le_of_subset`: `M_R(F) ⊆ M_J(F)`.
- `leviSchemeStandardLeviEquiv` and `leviSchemeStandardLeviEquiv_apply_coe`: the map `x ↦ j(x)`
  is an isomorphism of topological groups from `standardLeviPoints iL ν R` onto `M_R(F)`, each
  with its subspace topology.
- `inheritedCompactOpenNormalBasis_leviScheme`: assume
  `InheritedCompactOpenNormalBasis K0 M_R(F) B`. Then the literal intersections of
  `leviSchemeBasis i ν J B` with `standardLeviPoints iL ν R` form an inherited compact-open normal
  basis relative to `leviSchemeCompact K0 i ν J`.
- `leviSchemeBasis_basisClauses`: assume the inherited clause of `B` for every `R ⊆ Δ`, as
  supplied by `SimultaneousStandardBasisAt i ν K0`. Then both basis clauses of
  `SimultaneousStandardBasisAt iL ν (leviSchemeCompact K0 i ν J)` hold for `leviSchemeBasis i ν J B`:
  - the compact-open normal basis clause;
  - the inherited clause for every `R ⊆ simpleRelativeRoots iL ν`.

## Scope

This module does not treat the per-parabolic clauses of `SimultaneousStandardBasisAt`, namely the
compatible split component and `StandardParabolicBasisMember`. It does not assemble the full
property for `L`, and it makes no existence claim about `K0` or `B`.
