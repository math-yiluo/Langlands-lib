# The transfer of the local maps `W_{K_u} → W_{E/K}`

Lean module: `Langlands.ClassField.Global.RelativeWeilLocalTransfer`
(namespace `Langlands.ClassField.Global.RelativeWeilGroup`).

Derived infrastructure for condition 1 of `LocalInducedRestriction`, the transfer of the
local maps `localPlaceMap u : W_{K_u} → W_{E/K}`. It follows the computation of Tate,
*Number theoretic background* (1979), (1.2.2) and Proposition (1.6.1): on the image of a
local Weil group, the transfer to `C_E` is a product of Galois conjugates of the local
transfer `W_{K_u} → W_{E_w}^{ab}`. Local class field theory then turns the local transfer
into the inclusion `K_uˣ → E_wˣ` (Serre, *Local Fields*, XI §3, diagram (2)). This module
proves no local class field theory. Its final theorem takes the local transfer identity and
an idele identity as explicit hypotheses.

Setting: `F ⊆ K ⊆ E` with `E/F` and `E/K` Galois, a finite place `z` of `F`, a place `w` of `E`
above `z`, `u : FinitePlacesAbove K z`, and `ι : W_{F_z} →ₜ* W_{E/F}` (discrete topology on
`Gal(E/F)`) satisfying conditions 2 (`hι`) and 3 (`hι3`) of `IsLocalRelativeWeilMap`.
`x_u = placeRepresentative`, `ψ = localPlaceMap u`, `C_E = ideleClassSubgroup c K E`.

## Contents

- `twistedMap c K z w u : K_u →ₐ[F_z] E_w`, with
  `completionClosureEmbedding z w ∘ twistedMap = completionClosureEmbedding z u`
  (`completionClosureEmbedding_twistedMap`) and
  `twistedMap k = (projection x_u)⁻¹ k` on `K` (`twistedMap_algebraMap`). The image of `K_u` in
  `\bar{F_z}` lies in that of `E_w` (`completionClosureEmbedding_mem_range`), because `K`
  generates `K_u` over `F_z` (published `subalgebra_eq_top_of_algebraMap_mem`).
- The imported `Langlands.ClassField.Global.liesOver_finitePlaceEquiv` from
  `IdeleLocalInjectivity`: the pullback of a place above `z` along an `F`-automorphism of
  `E` lies above `z`.
- `ideleClassEquiv_ofAdicCompletion_units_map`: transport of a local unit `g'(a)` along
  `ideleClassEquiv ρ` is the image of `a` under `K_u → E_v`. Proof: the published
  `ideleClassEquiv_ofAdicCompletion`, then two `F_z`-algebra maps `K_u → E_v` that agree on
  `K` are equal (equalizer, `subalgebra_eq_top_of_algebraMap_mem`), with density of `F` in
  `F_z` for `F_z`-linearity of `finiteCompletionEquiv`.
- `localGaloisImage`: `localProjection (towerPadicField z u)` typed in
  `Field.absoluteGaloisGroup (u.adicCompletion K)`. All comparisons go through this type,
  which avoids unifying `towerPadicField z u` with `padicField u` (different prime indices).
- `upperEmbedding x g : E →+* \bar{K_u}`, `y ↦ λ(j_w((projection x)⁻¹ (projection g y)))`
  with `λ = extensionClosureLift` along `F_z → K_u`. Facts: it is `K`-linear
  (`upperEmbedding_algebraMap`). It determines the coset `g C_E`
  (`upperEmbedding_eq_iff`). Left multiplication by `ψ ℓ` composes it with the Galois image
  of `ℓ` (`upperEmbedding_localPlaceMap_mul`, from `projection_localPlaceMap_apply`, condition 2
  and `extensionClosureLift_galoisMap`). Every place embedding at `v` above `u` is
  of this form (`exists_upperEmbedding_eq`, via `AlgHom.restrictNormal'` and
  `projection_surjective`).
- `upperRepresentative v` for `v : FinitePlacesAbove E u`; `exists_eq_localPlaceMap_mul` (cover)
  and `upperRepresentative_injective` (disjointness) of the double cosets `ψ(W_{K_u}) t_v C_E`,
  from the lemmas of `RelativeWeilLocalCosets` applied one level up (base `K`, place `u`).
- `upperSubgroup = (completionWeilMap z w).range.comap (completionWeilMap z u)` and
  `mem_upperSubgroup_iff`: `l ∈ upperSubgroup ↔ ψ l ∈ C_E` (published `exact`, condition 2,
  `placeEmbedding_fixed_iff`, `extensionWeilMap_range`).
- `upperReciprocity e : upperSubgroup →* E_wˣ`, the reciprocity map of `E_w` read through
  `completionWeilMap`. `localPlaceMap_upperSubgroup` and `conj_localPlaceMap_upperSubgroup`
  (from condition 3 and `conjugation`) compute `ψ` and its conjugates on `upperSubgroup`.
- `upperTerm t a = (projection t⁻¹ · projection x_u · [a]_w)⁻¹ ∈ C_E` and
  `ideleTransfer_localPlaceMap`:
  `ideleTransfer c K E (ψ y) = ∏ v, upperTerm (t_v) (MonoidHom.transfer (upperReciprocity e) y)`,
  from the published `Langlands.GroupTheory.Transfer.transfer_comp_eq_prod_of_conj` (module
  `Langlands.GroupTheory.TransferDoubleCoset`) and the published `transfer_comp`.
- `upperRho v` (the automorphism `projection t_v⁻¹ ∘ projection x_u` over `F`) and
  `finitePlaceEquiv_upperRho`: `v` pulls back to `w`. Proof: the embedding
  `λ⁻¹ ∘ completionClosureEmbedding u v ∘ finiteCompletionEquiv` of the pulled-back completion is
  a Galois conjugate of its own closure embedding (`exists_eq_comp_completionClosureEmbedding`).
  It then agrees with the place embedding of `w`, and `eq_of_placeEmbedding_eq` gives equality.
- `upperTerm_twistedMap`: `upperTerm t_v (twistedMap a) = ([a]_v)⁻¹` with `[a]_v` the image under
  `completionMap u v`.
- `transfer_localPlaceMap_of_local`: given
  `htower : MonoidHom.transfer (upperReciprocity e) y = twistedMap (a)` and
  `hG : ∏ v, [a]_v = ideleClassInclusion [a]_u`, it proves
  `transfer c K E (ψ y) = ([a]_u)⁻¹` through the published
  `eq_transfer_of_ideleClassInclusion_eq`.

`htower` is the local transfer square for `K_u ⊆ E_w` along `twistedMap`, with the subgroup
`upperSubgroup` and the identification through `completionWeilMap`. `hG` is the place-by-place
description of the inclusion `C_K → C_E` on a local unit. The module
`Langlands.VirtualRepresentation.Global.RelativeWeilLocalRestrictionReduction` supplies both:
`htower` from the published `Langlands.LocalClassField.extensionWeilTransferReciprocity_tower`
(which assumes `ExtensionWeilTransferReciprocityStatement`), and `hG` from
`prod_ofAdicCompletion_eq_ideleClassInclusion`.
