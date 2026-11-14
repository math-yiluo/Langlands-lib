# Torus coincidences forced by `AvailableSpecialMaximalCompactExistence`

This module proves two implications out of the published target
`Langlands.BruhatTits.SpecialCompact.AvailableSpecialMaximalCompactExistence` (module
`Langlands.BruhatTits.SpecialCompact.AvailableExistenceStatement`). They record why that target
has no known proof, and why the corrected target
`AvailableSpecialMaximalCompactExistencePerLevi` (module
`Langlands.BruhatTits.SpecialCompact.AvailableExistencePerLeviStatement`) gives each standard
Levi its own assignment. The module proves no existence result.

## Declarations

- `heq_datum_base_i_of_eq`. Let `𝔅 : KPBuildingAssignment.{u}`, let `F` be a nonarchimedean
  local field, and let `G₁ G₂` be group schemes over `Spec F` with instances
  `IsAffineHom G₁.X.hom`, `IsAffineHom G₂.X.hom` and proofs `hG₁`, `hG₂` of
  `IsConnectedReductive`. If `G₁ = G₂`, then
  `HEq (𝔅.datum F G₁ hG₁).base.i (𝔅.datum F G₂ hG₂).base.i`.
- `heq_leviTorusHom_of_availableSpecialMaximalCompactExistence`. Assume
  `AvailableSpecialMaximalCompactExistence.{u}`. Let `F`, `G`, `hG`, `S`, `i`, `hi` and `ν`
  be as in that target, with `IsGenericCocharacter i ν`. For all
  `J₁, J₂ ⊆ simpleRelativeRoots i ν`, if
  `Standard.leviScheme i ν J₁ = Standard.leviScheme i ν J₂`, then
  `HEq (Standard.leviTorusHom i ν J₁) (Standard.leviTorusHom i ν J₂)`.
- `heq_torusHom_of_eq_leviScheme_of_availableSpecialMaximalCompactExistence`. Under the same
  assumptions, for every `J ⊆ simpleRelativeRoots i ν`, if `G = Standard.leviScheme i ν J`,
  then `HEq i (Standard.leviTorusHom i ν J)`.

The equalities of group schemes are equalities of terms of
`GroupScheme (Spec (CommRingCat.of F))`. The instance `IsAffineHom G.X.hom` is
`hG.isAffineHom`, and the instance on `Standard.leviScheme i ν J` is the one obtained from
`Standard.isClosedSubgroup_leviHom`, as in the target.

## Implemented proofs

`heq_datum_base_i_of_eq` substitutes `G₂ := G₁`. The two instances and the two
reductivity proofs are then proofs of the same propositions, hence definitionally equal,
and the two data coincide; `rfl` closes the goal.

For the two implications, the proof applies the target to `F, G, hG, S, i, hi, ν` and
obtains an assignment `𝔅`. The ambient clause gives `HEq (𝔅.datum F G hG).base.i i`. The
Levi clause at `J` gives a proof `hM` that `Standard.leviScheme i ν J` is connected reductive
and `HEq (𝔅.datum F (Standard.leviScheme i ν J) hM).base.i (Standard.leviTorusHom i ν J)`.
In the first implication the Levi clause is used at `J₁` and at `J₂`; in the second, the
ambient clause and the Levi clause at `J`. `heq_datum_base_i_of_eq`, applied to the assumed
equality of group terms, links the two data, and the three heterogeneous equalities are
composed with `HEq.symm` and `HEq.trans`.

## Why the conclusions are out of reach

`Standard.leviScheme i ν J` is the cut group scheme `Corepresented.intersectionScheme`, the
spectrum of a quotient of the coordinate ring of `G`. An equation between it and another
group-scheme term, such as the arbitrary `G` or the Levi for another `J`, is an equation
between structures whose fields are types (carriers of schemes, quotient rings). Lean cannot
refute such equations in general, because type formers such as quotients and spectra are not
provably injective. Under such an equation, nothing relates the two torus inclusions:
`Standard.leviTorusHom i ν J` is `i` factored through the closed inclusion
`Standard.leviHom i ν J`, and the assumed equation says nothing about these inclusions. No
proof of either conclusion is known. Any proof of `AvailableSpecialMaximalCompactExistence`
would give one, by the implications of this module.

## Provenance

This is internal content about the Library's formalization. It concerns the dependence of
`KPBuildingAssignment.datum` on group terms, not the mathematics of the sources. It cites no
literature.
