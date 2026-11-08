# Continuous characters of relative Weil groups factor through the transfer

Module `Langlands.ClassField.Global.RelativeWeilCharacterFactorization`, namespace
`Langlands.ClassField.Global.RelativeWeilGroup`. As in the published relative Weil group
modules, `Gal(E/F)` carries the discrete topology `relativeGaloisTopology`, a local instance
here, and `W_{E/F}` is `RelativeWeilGroup c F E` for a class family `c` and a finite Galois
extension `E / F` of number fields in `Type u`.

The module proves that the published transfer `transfer c F E : W_{E/F} → C_F` is continuous
and open. Its last theorem is `transferCharacterFactorization`, a proof of the published
proposition `TransferCharacterFactorizationStatement.{u}` of
`Langlands.ClassField.Global.RelativeWeilCharacterFactorizationStatement`, with no added
hypotheses.

## Declarations

- `transfer_comp_inclusion`: `transfer c F E ∘ inclusion c F E` is the idele-class norm
  `ideleClassNorm : C_E → C_F`. This is the published `transfer_inclusion`, written as an
  equality of functions.
- `continuous_transfer'`: the transfer is continuous. The published `continuous_transfer`
  needs the inclusion `C_F → C_E` to be a topological embedding. This version needs no
  hypothesis.
- `continuousTransfer` (definition): the transfer bundled as a continuous homomorphism
  `RelativeWeilGroup c F E →ₜ* IdeleClassGroup (𝓞 F) F`. Its underlying homomorphism is
  `transfer c F E`, so `continuousTransfer_apply` holds by `rfl`.
- `isOpenMap_transfer`: the transfer is an open map.
- `isQuotientMap_transfer`: a surjective transfer is a quotient map.
- `transferCharacterFactorization_of_surjective`: suppose the transfer is surjective and its
  kernel lies in the commutator subgroup of `W_{E/F}`. Then
  `TransferCharacterFactorization c F E` holds: every continuous `ξ : W_{E/F} →ₜ* ℂˣ` equals
  `χ ∘ transfer` for a continuous `χ : C_F →ₜ* ℂˣ`.
- `transferCharacterFactorization : TransferCharacterFactorizationStatement.{u}`.

## Proof

Continuity (`continuous_transfer'`). A homomorphism of topological groups is continuous if
it is continuous at `1` (Mathlib's `continuous_of_continuousAt_one`). The inclusion
`C_E → W_{E/F}` is an open embedding (published `isOpenEmbedding_inclusion`). So continuity of
the transfer at `1 = inclusion 1` is equivalent to continuity at `1` of
`transfer ∘ inclusion` (`IsOpenEmbedding.continuousAt_iff`). That composite is the continuous
idele-class norm.

Openness (`isOpenMap_transfer`). For a homomorphism of topological groups, being open means
`𝓝 1 ≤ map f (𝓝 1)` (Mathlib's `IsTopologicalGroup.isOpenMap_iff_nhds_one`). The idele-class
norm is an open map (the published `isOpenMap_ideleClassNorm` of
`Langlands.Global.AdelicFunctoriality.IdeleNormOpen`), so `𝓝 1` in `C_F` lies below the image
of `𝓝 1` in `C_E` under the norm. That image equals the image under the transfer of
`map inclusion (𝓝 1)`, and this filter is `𝓝 1` in `W_{E/F}` because the inclusion is an open
embedding (`IsOpenEmbedding.map_nhds_eq`).

Factorization (`transferCharacterFactorization_of_surjective`). A continuous, open,
surjective map is a quotient map (`IsOpenMap.isQuotientMap`). The character `ξ` has values in
the commutative group `ℂˣ`, so the commutator subgroup lies in its kernel
(`Abelianization.commutator_subset_ker`). By hypothesis the kernel of the transfer does too.
Mathlib's `MonoidHom.liftOfSurjective` then gives a homomorphism `χ₀ : C_F →* ℂˣ` with
`χ₀ (transfer t) = ξ t` (`MonoidHom.liftOfRightInverse_comp_apply`). It is continuous by
`IsQuotientMap.continuous_iff`, because `χ₀ ∘ transfer = ξ` is continuous.

Final theorem (`transferCharacterFactorization`). `IsArithmeticClassFamily c` supplies a
family `I` of local invariant families together with the hypotheses of the published
`RelativeWeilTransferReciprocityStatement`. Its proof `relativeWeilTransferReciprocity` gives
that the transfer is surjective with kernel equal to the commutator subgroup. Then apply
`transferCharacterFactorization_of_surjective`.

## Relation to the source

John Tate, *Number theoretic background*, Proc. Sympos. Pure Math. 33, Part II (1979), 3–26
(registered `tate-1979-number-theoretic-background`), §1.1, printed pp.3–4 (PDF pp.12–13).
In the definition (1.1) of a Weil group, `r_E : C_E → W_E^{ab}` is an isomorphism of
topological groups. The transfer is defined on the first page of §1. Diagram (1.2.2) says
that, through `r_E` and `r_{E'}`, the map `W_E^{ab} → W_{E'}^{ab}` induced by the inclusion
is the norm `C_E → C_{E'}`. For `E' = F` this is the counterpart of the Library's
`transfer_inclusion`: `C_E` goes into `W_{E/F}` and then by the transfer to `C_F`, and the
composite is the idele-class norm.

`continuousTransfer` and the factorization are derived from this, not stated by Tate. For the
Library's relative Weil group they give the topological half of `W_{E/F}^{ab} ≅ C_F`, in the
form needed for characters with values in `ℂˣ`. The algebraic half is the published transfer
reciprocity. The route is internal to the Library: continuity and openness come from the norm
on the open subgroup `C_E`. Openness of the idele-class norm is the published `IdeleNormOpen`,
which rests on Artin–Tate, Chapter VI §3. The definition `continuousTransfer` is internal
packaging of `transfer c F E` with its continuity.
