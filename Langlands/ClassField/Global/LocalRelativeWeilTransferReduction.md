# Reduction of local transfer reciprocity to the local transfer square

Lean module: `Langlands.ClassField.Global.LocalRelativeWeilTransferReduction`.

Authorship: drafted by Worker 1835 in the shared draft of task
`960e8dac-1593-4e9e-a96e-20cc689cb4aa`; updated to the current Library and submitted by
Worker 5086.

This module reduces the published
`Langlands.ClassField.Global.RelativeWeilGroup.LocalTransferReciprocityStatement`
to the published local proposition
`Langlands.LocalClassField.ExtensionWeilTransferReciprocityStatement` (the
field-inclusion/transfer square of local class field theory, Jean-Pierre Serre,
*Local Fields*, GTM 67 (1979), Chap. XI, §3, diagram (2), p.170). The main result
is the conditional theorem `localTransferReciprocity_of_square`. It assumes the
local square as a hypothesis, so it does not prove the target by itself. The
unconditional theorem `localTransferReciprocity` is in the companion module
`Langlands.ClassField.Global.LocalRelativeWeilTransferProof`, which supplies the
published proof `Langlands.LocalClassField.extensionWeilTransferReciprocity` of the
square.

The argument is the one sketched in item 4 of "Relation to the source" in the
Markdown of `LocalRelativeWeilTransferStatement`, following John Tate, *Number
theoretic background*, Proc. Sympos. Pure Math. 33, Part II (1979), Proposition
(1.6.1), p.8. Every lemma below is internal to this proof. All of them work for an
arbitrary class family `c`.

## Setting and notation

Namespace `Langlands.ClassField.Global.RelativeWeilGroup`. Throughout:

- `c : FundamentalClass.ClassFamily.{u}`, and `F E : Type u` are number fields
  with `[Algebra F E]` and `[IsGalois F E]`.
- `z` is a finite place of `F`, and `w` is a finite place of `E` with
  `[w.asIdeal.LiesOver z.asIdeal]`.
- `W_{E/F} = RelativeWeilGroup c F E` has the published `projection` to
  `Gal(E/F)`, the published `inclusion : C_E → W_{E/F}`, and the subgroup
  `ideleClassSubgroup c F E`, which is the range of `inclusion` and the kernel of
  `projection`.
- `W_{F_z}` is `Weil.Local.localWeilGroup (padicField z)`, and `W_{E_w}` is
  `Weil.Local.localWeilGroup (towerPadicField z w)`. The published
  `completionWeilMap z w : W_{E_w} → W_{F_z}` is injective, and its range has
  finite index.
- `D_w ⊆ Gal(E/F)` is the range of the published
  `FundamentalClass.decompositionHom z w : Gal(E_w/F_z) →* Gal(E/F)`.
- `e` is a reciprocity candidate of `E_w`, and
  `ι : W_{F_z} →ₜ* W_{E/F}` satisfies the published `IsLocalRelativeWeilMap z w e ι`
  (written `hι`). Its three parts are: `e` satisfies the geometric Weil
  reciprocity relation for `E_w`; the image of `ι g` in `Gal(E/F)` acts on `E`
  as `g` acts on the closure of `F_z`, through `E ⊆ E_w`; and
  `ι (completionWeilMap z w y)` is the inverse of the image of `e(y)` under
  `E_wˣ → C_E → W_{E/F}`.

## Restriction to `E_w`

- `closureAlgebra z w` (an `abbrev`) makes the closure of `F_z` an `E_w`-algebra
  through the published `completionClosureEmbedding z w`, and
  `closureAlgebra_isScalarTower z w` shows that this is a tower over `F_z`.
- `localRestriction z w g` is the restriction to `E_w` of the image of `g ∈ W_{F_z}`
  in the absolute Galois group of `F_z` (Mathlib's `AlgEquiv.restrictNormal`; `E_w`
  is Galois over `F_z` by the published `isGalois_adicCompletion`).
- `completionClosureEmbedding_localRestriction z w g y` is the defining property:
  embedding `localRestriction z w g y` in the closure gives the image of `g` applied
  to the embedded `y`.
- `projection_eq_decompositionHom hι g`: the image of `ι g` in `Gal(E/F)` is
  `decompositionHom z w (localRestriction z w g)`. Proof: both sides are compared on
  `E`, after embedding in `E_w` and then in the closure (both injective). The published
  `algebraMap_decompositionHom`, the restriction property and the second part of `hι`
  close the goal.

## The preimage of `C_E` and the image in `Gal(E/F)`

- `comap_ideleClassSubgroup_eq hι`: the preimage under `ι` of `ideleClassSubgroup c F E`
  is the range of `completionWeilMap z w`.
  - Inclusion `⊆`: if `ι x ∈ C_E`, then `projection (ι x) = 1`. So
    `localRestriction z w x = 1`, because `decompositionHom z w` is injective
    (published `decompositionHom_injective`). By the published
    `extensionWeilMap_range` and `extensionGaloisMap_range`, the range of
    `completionWeilMap z w` is the preimage of the fixing subgroup of the image of
    `E_w`. The element `x` fixes that image (`mem_extensionIntermediateField`).
  - Inclusion `⊇`: this is the third part of `hι`.
- `ker_projection_comp_eq hι`: the same subgroup is the kernel of
  `projection ∘ ι`.
- `card_range_decompositionHom z w`: `D_w` has `[E_w : F_z]` elements, written with the
  published `Weil.Local.extensionDegree` of `completionPadicAlgHom z w`. This uses
  injectivity of `decompositionHom z w` and Mathlib's `IsGalois.card_aut_eq_finrank`.
- `range_projection_comp_eq hι`: the image of `W_{F_z}` in `Gal(E/F)` is exactly `D_w`.
  The image is contained in `D_w` by `projection_eq_decompositionHom`. The orders
  agree: the image has order equal to the index of the kernel
  (`Subgroup.index_ker`). That kernel is the range of `completionWeilMap z w`, whose
  index is `[E_w : F_z]` by the published `extensionWeilMap_range_index`. No density
  argument is used.

## Transfer

- `transfer_comp_inclusion_of_eq h ϕ g`: for subgroups `K = R` of finite index and
  `ϕ : R →* A`, the transfer of `ϕ ∘ inclusion` equals the transfer of `ϕ`.
- The published instance `completionWeilMap_range_finiteIndex` from
  `Langlands.VirtualRepresentation.Global.RelativeWeilLocalRestrictionStatement`
  supplies finite index of the range of `completionWeilMap z w`, using
  `extensionWeilMap_range_finiteIndex`. The reduction imports and reuses this instance.
- `rangeReciprocity z w e`: the homomorphism from the range of `completionWeilMap z w`
  to `E_wˣ` that inverts `completionWeilMap z w` (published
  `InductionAlong.rangeInverse`) and then applies the reciprocity map of `e`
  (`LocalFactor.RankOne.reciprocityUnits`). Its transfer `W_{F_z} → E_wˣ` is the left
  side of the local square. `rangeReciprocity_apply` evaluates it on
  `completionWeilMap z w y`.
- `ideleClassSubgroupHom c F E` (an `abbrev`) is the identification of
  `ideleClassSubgroup c F E` with `C_E` used in the published `ideleTransfer`. It is
  written with the discrete topology `relativeGaloisTopology` declared as a local
  instance, as in the published definition. The type of `ι` uses the Krull topology
  on `Gal(E/F)`.
- `conjugateInvClass F E w σ`, for `σ ∈ Gal(E/F)`, is the homomorphism
  `E_wˣ → C_E`, `a ↦ σ([a]_w)⁻¹`. Here `[a]_w` is Mathlib's
  `IdeleClassGroup.ofAdicCompletion`, and `σ` acts on `C_E` by the published
  `relativeIdeleClassAut`. `conjugateInvClass_apply` unfolds it.
- `comp_conjInv_comp_subgroupComap hι v`: on the preimage under `ι` of `C_E`, the
  homomorphism `ψ ∘ conjInv v ∘ ι` equals `conjugateInvClass (projection v⁻¹)` after
  `rangeReciprocity z w e`. Here `ψ = ideleClassSubgroupHom c F E`, and
  `conjInv v` is the published conjugation `h ↦ v⁻¹ h v`. Proof: write the element as
  `completionWeilMap z w y`. By the third part of `hι`, `ι` sends it to
  `inclusion([e(y)]_w)⁻¹`. The published `conjugation` theorem of `RelativeWeilGroup`
  turns `v⁻¹ · inclusion(x) · v` into `inclusion` of the action of `projection v⁻¹` on
  `x`. Then the published `ideleClassSubgroupEquiv_inclusion` applies.
- `transfer_comp_conjInv_comp_subgroupComap hι v y`: the corresponding transfers
  `W_{F_z} → C_E` agree. The transfer of the left side at `y` is
  `conjugateInvClass (projection v⁻¹)` of the transfer of `rangeReciprocity z w e`
  at `y`. This follows from the previous lemma, `transfer_comp_inclusion_of_eq` and
  the published `Langlands.GroupTheory.Transfer.transfer_comp`.
- `ideleTransfer_eq_of_transfer_rangeReciprocity hι a y hy`: suppose the transfer of
  `rangeReciprocity z w e` at `y ∈ W_{F_z}` is the image of `a ∈ F_zˣ` in `E_wˣ`
  under `FiniteExtension.completionMap z w`. Then the published
  `ideleTransfer c F E (ι y)` equals `(ideleClassInclusion [a]_z)⁻¹`.

  Proof. Choose representatives `σ i` (Mathlib's `Quotient.out`) of the cosets
  `Gal(E/F) / D_w`, and lifts `t i ∈ W_{E/F}` with `projection (t i) = (σ i)⁻¹`
  (published `projection_surjective`). Using `range_projection_comp_eq`, every `g` in
  `W_{E/F}` is `ι l · t i · h` with `h ∈ C_E`, and the index `i` is unique. These are
  the hypotheses of `transfer_comp_eq_prod_of_normal` from
  `Langlands.GroupTheory.TransferDoubleCoset`. It writes
  `ideleTransfer c F E (ι y)` (published `ideleTransfer_apply`) as the product over
  `i` of the transfers of `ψ ∘ conjInv (t i) ∘ ι`. By the previous lemma and `hy`,
  the `i`-th factor is `σ i([a]_w)⁻¹`, where `a` is read in `E_wˣ`. The product of
  the `σ i([a]_w)` is `ideleClassInclusion [a]_z` by
  `prod_relativeIdeleClassAut_ofAdicCompletion_of_coset` from
  `Langlands.ClassField.Global.IdeleClassPlaceProduct`. Its coset hypothesis is
  that every `τ` satisfies `(σ i)⁻¹ τ ∈ D_w` for exactly one `i`, which holds for
  coset representatives.

## The conditional theorem

- `localTransferReciprocity_of_square
  (hsq : LocalClassField.ExtensionWeilTransferReciprocityStatement.{u, u}) :
  LocalTransferReciprocityStatement.{u}`.

  Proof. Fix the data of the target, a candidate `ez` of `F_z` satisfying the
  geometric Weil reciprocity relation, and `g ∈ W_{F_z}`. The published
  `eq_transfer_of_ideleClassInclusion_eq` reduces the claim to an identity in `C_E`:
  `ideleClassInclusion [ez(g)]_z⁻¹ = ideleTransfer c F E (ι g)`. By
  `ideleTransfer_eq_of_transfer_rangeReciprocity` with `a = ez(g)`, it suffices that
  the transfer of `rangeReciprocity z w e` at `g` is the image of `ez(g)` in `E_wˣ`.
  This is `hsq` applied to the prime `residuePrime z`, the fields `padicField z` and
  `towerPadicField z w`, the embedding `completionPadicAlgHom z w`, the candidates `ez`
  and `e`, the relation for `ez`, the first part of `hι`, and `g`.

The hypothesis `hsq` is the published square at universes `{u, u}`. It is proved in
the Library as `Langlands.LocalClassField.extensionWeilTransferReciprocity` (module
`Langlands.ClassFieldTheory.Local.WeilTransferReciprocityProof`). This module does not
import that proof; `Langlands.ClassField.Global.LocalRelativeWeilTransferProof`
combines the two.

## Public results used

From the Library: `IsLocalRelativeWeilMap`, `completionWeilMap`,
`completionClosureEmbedding`, `completionClosureEmbedding_algebraMap`,
`isGalois_adicCompletion`, `FundamentalClass.decompositionHom`,
`algebraMap_decompositionHom`, `decompositionHom_injective`,
`Weil.Local.extensionWeilMap_range`, `Weil.Local.extensionGaloisMap_range`,
`Weil.Local.mem_extensionIntermediateField`, `Weil.Local.extensionWeilMap_range_index`,
`Weil.Local.extensionWeilMap_range_finiteIndex`, `Weil.Local.extensionWeilMap_injective`,
`InductionAlong.rangeInverse`, `InductionAlong.rangeInverse_apply`,
`RelativeWeilGroup.projection`, `projection_surjective`, `inclusion`, `conjugation`,
`ideleClassSubgroup`, `exact`, `ideleClassSubgroupEquiv`,
`ideleClassSubgroupEquiv_inclusion`, `relativeIdeleClassAction`,
`relativeGaloisTopology`, `relativeIdeleClassAut`, `ideleClassEquiv`, `ideleTransfer`,
`ideleTransfer_apply`, `eq_transfer_of_ideleClassInclusion_eq`,
`Langlands.GroupTheory.Transfer.conjInv`, `coe_conjInv`, `transfer_comp`,
`LocalFactor.RankOne.reciprocityUnits`, `completionPadicAlgHom`, `residuePrime`,
`padicField`, `towerPadicField`, and the statement
`LocalClassField.ExtensionWeilTransferReciprocityStatement`.

From the published helper modules:
`Langlands.GroupTheory.Transfer.transfer_comp_eq_prod_of_normal`
(`Langlands.GroupTheory.TransferDoubleCoset`) and
`Langlands.ClassField.Global.prod_relativeIdeleClassAut_ofAdicCompletion_of_coset`
(`Langlands.ClassField.Global.IdeleClassPlaceProduct`).
