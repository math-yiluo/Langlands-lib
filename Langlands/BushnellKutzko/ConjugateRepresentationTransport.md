# Transport of representations of subgroups by conjugation

The module `Langlands.BushnellKutzko.ConjugateRepresentationTransport` moves representations
of subgroups of a group `G` along conjugation by an element `g`, and shows that for
`G = Aut_F(V)` this preserves the conditions of BK93 Chapter 5 used to define simple types.

## Groups

For subgroups `K`, `K'` and a proof `h : K' = gKg⁻¹` (`conjugateSubgroup g K`),
`conjEquivOfEq g h : K ≃* K'` is `k ↦ gkg⁻¹` (`coe_conjEquivOfEq`); its inverse is
`k' ↦ g⁻¹k'g` (`coe_conjEquivOfEq_symm`). A representation `ρ` of `K` is transported to the
representation `ρ ∘ (conjEquivOfEq g h)⁻¹` of `K'`. Taking `K'` through an equation, rather
than the literal `conjugateSubgroup g K`, lets the transported representation live on a
subgroup that is only provably equal to the conjugate, such as the groups `J(β, 𝔄)` of a
conjugated stratum.

- `mem_conjugateSubgroup_iff`: `x ∈ gKg⁻¹ ↔ g⁻¹xg ∈ K`; `conjSubgroupEquiv_symm_val`
  computes the inverse of `conjSubgroupEquiv`; `conjugateSubgroup_inf` says conjugation
  commutes with intersections.
- `conjEquivOfEq_symm_inclusion`: the transport is compatible with inclusions `K₁ ≤ K₂`.
- `isIrreducible_comp_mulEquiv`: pulling back along a group isomorphism preserves
  irreducibility (the lattices of subrepresentations are order isomorphic).
- `equivComp`, `equivOfPullback`, `intertwiningMapComp`: equivalences and intertwining maps
  of representations pull back along homomorphisms, with the same underlying linear map.
- `IsPairIsomorphic.conj`: if `(J₁, ρ₁) ≅ (J₂, ρ₂)` (`IsPairIsomorphic`) and `J₂' = gJ₂g⁻¹`,
  then `(gJ₁g⁻¹, ρ₁^{g⁻¹}) ≅ (J₂', ρ₂ ∘ (conjEquivOfEq g _)⁻¹)`, where `ρ₁^{g⁻¹}` is
  `conjRepresentation g ρ₁`.

## Representations of subgroups of `Aut_F(V)`

Let `f` be the linear automorphism given by `g`, and `L.linearEquivMap f` the image of a
lattice chain `L`.

- `IsSmoothRepresentation.conj`: transport preserves smoothness, with the image chain as
  witness (`LatticeChain.Corresponds.mem_unitFiltration`).
- `unitFiltration_linearEquivMap`: `U^m(g𝔄g⁻¹) = gU^m(𝔄)g⁻¹`.
- `centralizerUnitGroup_endConj`: `B_{gβg⁻¹}^× = gB_β^×g⁻¹`, since conjugation is a ring
  automorphism of `End_F(V)`.
- `relativeUnitFiltration_linearEquivMap`: the same for `relativeUnitFiltration`, the
  intersection of these two groups.
- `IsHeisenbergRepresentation.conj` (BK93 (5.1.1)): if `H^1` and `J^1` of the new data are
  the conjugates of those of the old data, the transported representation is a Heisenberg
  representation of the transported character. Finite dimensionality and the carrier are
  unchanged; irreducibility uses `isIrreducible_comp_mulEquiv`; the nonzero intertwining map
  from the character is the same linear map.
- `IsBetaExtension.conj` (BK93 (5.2.1)): for the element `gβg⁻¹` and groups `J^1`, `J` equal
  to the conjugates, transport carries `β`-extensions to `β`-extensions. The restriction to
  `J^1` is transported by `equivComp`. Intertwining by `y ∈ B_{gβg⁻¹}^×` follows from
  intertwining by `g⁻¹yg ∈ B_β^×` and `selfIntertwines_comp_mulEquiv_iff` (module
  `IntertwiningTransport`) applied to conjugation by `g`.

## Sources

These are the change-of-coordinates properties of the constructions of Bushnell and Kutzko,
*The admissible dual of GL(N) via compact open subgroups* (1993): smooth representations,
(5.1.1), printed p. 158, `β`-extensions (5.2.1), printed p. 166, and the pairs `(J, λ)` of
(5.5.10), printed pp. 184–185. BK93 does not state them separately. Literature ID
`bushnell-kutzko-1993-admissible-dual-gln`, SHA-256
`811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`.
