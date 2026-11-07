# Continuous characters of relative Weil groups and the transfer

## Statement

The module defines two propositions in namespace
`Langlands.ClassField.Global.RelativeWeilGroup`. As in the published relative Weil group
modules, `Gal(E/F)` carries the discrete topology `relativeGaloisTopology`, a local instance
here. By `krullTopology_eq_relativeGaloisTopology` it equals the Krull topology for a finite
extension.

- `TransferCharacterFactorization c F E`: for every continuous character
  `ξ : RelativeWeilGroup c F E →ₜ* ℂˣ` there is a continuous character
  `χ : NumberField.IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ` of the idele class group `C_F` with
  `ξ t = χ (transfer c F E t)` for every `t ∈ W_{E/F}`. Here `transfer c F E : W_{E/F} → C_F`
  is the published transfer of `Langlands.ClassField.Global.RelativeWeilTransfer`.
- `TransferCharacterFactorizationStatement`: `TransferCharacterFactorization c F E` holds for
  every class family `c` with `IsArithmeticClassFamily c` (the published predicate of
  `Langlands.Automorphic.AssociatedFactorStatement`) and every finite Galois extension `E / F`
  of number fields in `Type u`.

The character `χ` is unique, because the transfer is surjective at an arithmetic class
family. Uniqueness is not part of the statement.

## Relation to the source

John Tate, *Number theoretic background*, Proc. Sympos. Pure Math. 33, Part II (1979), 3–26
(registered `tate-1979-number-theoretic-background`), §1.1, printed p.3 (PDF p.12). A Weil group
comes with isomorphisms of topological groups `r_E : C_E → W_E^{ab}`, where `G^{ab}` is the
quotient of `G` by the closure of its commutator subgroup. In (W1) the composite with the
projection to the Galois group is the reciprocity homomorphism.

The statement is a derived relative form of the topological part of this. The Library's
`W_{E/F}` is the class extension of `Gal(E/F)` by `C_E` at the class `c F E`, and its transfer
`W_{E/F} → C_F` plays the role of the inverse of `r_F` on `W_{E/F}^{ab}`. Two consequences of
Tate's description are relevant:

1. The algebraic part, that the transfer is surjective with kernel the commutator subgroup,
   is the published `RelativeWeilTransferReciprocityStatement`, proved as
   `relativeWeilTransferReciprocity`.
2. The topological part says the induced bijection `W_{E/F}^{ab} → C_F` is a homeomorphism.
   For characters with values in the Hausdorff group `ℂˣ`, which factor through
   `W_{E/F}^{ab}`, it gives exactly `TransferCharacterFactorization`. This module states only
   that consequence for characters.

The hypothesis `IsArithmeticClassFamily c` makes the transfer surjective, so it is the
setting where Tate's isomorphism applies. Without surjectivity a character of `W_{E/F}`
could not in general be written through the transfer.

## Why it is needed

The proof of `Langlands.Global.FunctionalEquationComparison.RelativeWeilTwistFunctionalEquationStatement`
(task `cc3ec74b-6eb5-4fd8-af55-97f37ce4d76c`) writes a twisted pair of representations of
`W_{E/F}` as a virtual sum of inductions of continuous characters `θ` of the groups `W_{E/K}`
(the published `RelativeWeilGroup.exists_twist_decomposition`). Applying the Hecke functional
equation over `K` needs each `θ` written as `η ∘ transfer` for a Hecke character
`η : HeckeCharacter K`, which is a continuous character of `C_K`. This proposition supplies
that `η`.

## A possible route

This is a suggestion only. The transfer is continuous, because it is continuous on the open
subgroup `C_E`, where it is the idele-class norm (`transfer_inclusion`). For a homomorphism,
being open on an open subgroup implies being open. If the idele-class norm `C_E → C_F` is an
open map, the transfer is therefore open, and the factorization of `ξ` through the surjective
transfer is continuous. Openness of the norm reduces to local statements through the open
S-unit ideles (`Langlands.Global.Arithmetic.SUnitIdeleTopology`). At unramified places every
valuation unit is a local norm of a valuation unit
(`FiniteExtension.exists_localNorm_eq_of_ramificationIdx_eq_one`). At the finitely many other
places one needs the local norm maps `L_w^× → K_v^×` to be open. Their images contain
neighbourhoods of `1` (`LocalNormNeighborhoodStatement` and its proof), so they are open
subgroups, and openness of the maps onto them follows, for instance, from the open mapping
theorem `MonoidHom.isOpenMap_of_sigmaCompact`.
