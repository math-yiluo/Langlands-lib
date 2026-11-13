# Exact virtual groups along an isomorphism of p-adic fields

Worker 5130, Task 5230. Internal derived infrastructure; no external source.

Two carrier-universe lemmas for the Library's `ExactGrothendieckGroup.universeMap`:
`degree_universeMap` (degree is preserved) and `universeMap_continuousTwist` (it
commutes with twisting by a continuous character). Both are checked on generators
with `universeModelEquiv`.

For `g : F ≃ₐ[ℚ_p] E` and `L : Extension F`, `virtualMap F E g L` maps
`Virtual F L` to `Virtual E σ(L)`. It restricts along
`subgroupWeilEquiv L : W_E(σ(L)) ≃ₜ* W_F(L)` and then applies `universeMap`, which
moves the carrier universe from `max u₁ uV` to `max u₂ uV`. Properties:

* `virtualMap_ofRepresentation`: on a generator, the value is the class of any
  representation equivalent to the restriction.
* `degree_virtualMap`: the degree is preserved.
* `virtualMap_characterClass`: a character class goes to the class of the character
  precomposed with `subgroupWeilEquiv`.
* `virtualMap_continuousTwist` and `virtualMap_virtualTwist`: twisting commutes with
  the map, including the spectral twist by `|·|^s`. `localDegree_weilEquiv`,
  `baseCardinality_eq` and `character_comp` supply the degree and the residue
  cardinality inputs.
* `virtualMap_induce`: common-closure induction from `L` to `M ≤ L` commutes with the
  map. On generators, `restrictInducedEquiv` identifies the restriction to
  `W_E(σ(M))` of the induced representation with the representation induced from
  `W_E(σ(L))`. It uses the Library's `restrictInduceEquiv` with the nested subgroup
  map `nestedSubgroupHom` (`restrictInduceNestedEquiv`), the identity intertwiner
  `nestedRestrictEquiv` for the commuting square of nested and transport maps, and
  `induceEquivOfEquiv`. The proof follows the Library's
  `induce_bot_eq_continuousInduceAlong`.
