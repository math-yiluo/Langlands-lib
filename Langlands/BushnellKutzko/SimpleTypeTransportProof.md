# Transport of simple type data and conjugacy of principal orders: proof

`Langlands.BushnellKutzko.simpleTypeTransport` proves
`Langlands.BushnellKutzko.SimpleTypeTransportStatement.{uF, uV, uW}`, with the field, the
vector space and the representation carrier in independent universes. Fix `g ∈ Aut_F(V)` and
let `f` be the linear automorphism it defines.

## Supporting results in this module

- `isPrincipalOrder_linearEquivMap`: if the order of `L` is principal, so is the order of
  `L.linearEquivMap f`. A principal chain `M` with the same order as `L` is carried to the
  principal chain `M.linearEquivMap f` (`LatticeChain.isPrincipal_linearEquivMap`), whose
  order is that of `L.linearEquivMap f` by `LatticeChain.Corresponds.order_eq_iff`.
- `LatticeChain.semilinearImage_linearEquivMap`: `f` carries `L` onto `L.linearEquivMap f`
  in the sense of `LatticeChain.SemilinearImage`, with the identity of `𝒪_F`.

## Kind (b)

`isLevelZeroSimpleTypeData_conj` takes level-zero data for `(J, ρ)` on the chain `L` to
data for `conjRepresentation g ρ` on `L' = L.linearEquivMap f` with the same `e`; the
periods agree by `LatticeChain.period_linearEquivMap`. The cuspidal representation `σ₀` of
`GL_f(k_F)` is unchanged. The layer bases are the bases transported along
`SemilinearImage.layerEquiv`, and the reduction map is `φ` composed with `u ↦ g⁻¹ug` on
`U(𝔄') = gU(𝔄)g⁻¹` (`unitFiltration_linearEquivMap`). Since the residue-field isomorphism
is the identity (`ResidueField.mapEquiv_refl`), `SemilinearImage.isLayerReduction` gives the
layer reduction. Triviality on `U^1(𝔄')` follows from
`U^1(𝔄') = gU^1(𝔄)g⁻¹`, and the isomorphism of pairs from `IsPairIsomorphic.conj`.

## Kind (a)

`isSimpleTypeDataOver_conj` follows the proof of `simpleCharacterConjugation` (module
`SimpleCharacterConjugationProof`). The new stratum is `T = Stratum.transport S f L'` on
`L' = S.chain.linearEquivMap f`, with the same `n` and `r` and element `gβg⁻¹`; it is simple
by `Stratum.Corresponds.isSimple_iff`, and its order is principal by
`isPrincipalOrder_linearEquivMap`. The defining sequence is the image `q'` of `q` under
`Stratum.DefiningSequenceChoice.transport`. Then `H^k` and `J^k` of `T` computed from `q'`
are `gH^kg⁻¹` and `gJ^kg⁻¹` (`LatticeChain.Corresponds.simpleHGroup_eq_of_eq`,
`simpleJGroup_eq_of_eq` and `map_unitsConj_toLinearEquiv`).

The character is `θ' = θ ∘ (h ↦ g⁻¹hg)` on `H^1` of `T`. It corresponds to `θ` in the sense
of `CharacterCorresponds`, so `(H', θ') = CharacterPair.conj g⁻¹ (H, θ)` by
`characterPair_eq_conj`, and `θ'` is a simple character by
`LatticeChain.Corresponds.mem_simpleCharacters_of_eq`. The Heisenberg representation, the
`β`-extension and the representation `σ` of `J` are composed with `j ↦ g⁻¹jg`
(`IsHeisenbergRepresentation.conj`, `IsBetaExtension.conj`, `IsSmoothRepresentation.conj`),
and `(gJg⁻¹, ρ^{g⁻¹}) ≅ (J(gβg⁻¹, g𝔄g⁻¹), κ' ⊗ σ')` by `IsPairIsomorphic.conj`.

For the finite-field data let `E = F[β]` and `E' = F[gβg⁻¹]`, with the field structures
given by simplicity. Conjugation restricts to an `F`-algebra isomorphism `E ≃ E'`
(`elementAlgebraAlgConj`), hence to `𝔬_E ≃ 𝔬_{E'}` (`subfieldIntegersAlgEquiv`) and
`k_E ≃ k_{E'}` (`ResidueField.mapEquiv`). Since `f(av) = (gag⁻¹) f(v)` for `a ∈ 𝔬_E`, the map
`f` carries the `𝔬_E`-lattice chain of `S` onto the `𝔬_{E'}`-lattice chain of `T` in the
sense of `LatticeChain.SemilinearImage`. So both chains have the period `e`
(`SemilinearImage.period_eq`). The new cuspidal representation is `σ₀` pulled back along
`GL_f(k_{E'}) ≃ GL_f(k_E)`; it is irreducible by `isIrreducible_comp_mulEquiv` and cuspidal
by `isCuspidal_comp_generalLinearMapEquiv`. The layer bases are transported, and the
reduction map is `φ` composed with `u ↦ g⁻¹ug` on
`U(𝔅_{gβg⁻¹}) = gU(𝔅_β)g⁻¹` (`relativeUnitFiltration_linearEquivMap`) followed by the
entrywise residue-field isomorphism. `SemilinearImage.isLayerReduction` gives the layer
reduction. The restriction of `σ'` to `U(𝔅_{gβg⁻¹})` is equivalent to the inflated tensor
power by `equivOfPullback`, with `tensorPowerRepresentation_comp_piMap`.

## Principal orders

The divisibility is `LatticeChain.period_dvd_finrank_of_isPrincipalOrder`, and the conjugacy
of principal orders of equal period is `LatticeChain.exists_order_eq_of_isPrincipalOrder`,
both from the module `PrincipalOrderConjugacy`.

The hypotheses `IsBKAdditiveCharacter ψF` and `1 ≤ N` of the statement are not used
separately: the first is part of the kind (a) data and is carried over unchanged.

## Sources

The statement and its sources are those of `SimpleTypeTransportStatement`. Bushnell and
Kutzko, *The admissible dual of GL(N) via compact open subgroups* (1993), §1.1, printed
pp. 22–23 (PDF pp. 34–35), and (5.5.10), printed pp. 184–185 (PDF pp. 196–197). Literature
ID `bushnell-kutzko-1993-admissible-dual-gln`, SHA-256
`811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`. Bushnell and Kutzko,
*Simple types in GL(N): computing conjugacy classes* (1994), §3, printed p. 126 (PDF
p. 139). Literature ID `bushnell-kutzko-1994-simple-types-conjugacy-classes`, SHA-256
`fd2077476192d9db15188feea9ff73774fe96296a2a31412d612f2081581efaa`.
