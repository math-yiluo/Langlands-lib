# Restriction of compact sections along an equivariant closed embedding

Helper module for the proof of Renard III.3.1, Proposition
(`Langlands.Sheaf.Renard.CoinvariantStatements.FibreCoinvariantStatement`).
Worker 136 wrote it for Task 5593. All declarations have prefix
`Langlands.Sheaf.Renard.FibreCoinvariantRestriction`.

## Setting

`G` is a group with a topology. `X` and `Z` are topological spaces with
continuous `G`-actions (`ContinuousSMul`). `f : C(Z, X)` is continuous and
equivariant (`hf : ∀ g z, f (g • z) = g • f z`). For an action sheaf
`F : ActionSheaf G X`, `res f hf F` abbreviates the published equivariant inverse
image `(actionInverseImage f hf).obj F`. In the main proof `f` is the inclusion
`InvariantFibres.inclusion q y` of the fibre `q⁻¹(y)`, and `res` is exactly the
`InvariantFibres.restriction` used in the target statement. The module is stated
for a general `f` because nothing about fibres is needed.

## Declarations

- `topHom` and `globalRestrict F`. `globalRestrict` maps global sections of `F`
  to global sections of `res f hf F`. It is the published inverse-image unit
  `InverseImageStalks.unit f hf F` at the top open, followed by restriction along
  `topHom`, which is the inclusion of the top open of `Z` into the preimage of
  the top open of `X`.
- `germ_globalRestrict`: for every `z : Z`, the germ at `z` of the restricted
  section is the image of the germ of `a` at `f z` under the published stalk
  isomorphism `InverseImageStalks.stalkIso f hf F z`. Proof: Mathlib's
  `germ_res_apply` and the published `InverseImageStalks.germ_stalkIso_hom`.
- `support_globalRestrict_subset`: the support of the restricted section lies in
  `f ⁻¹'` of the support of `a`. This is immediate from the germ formula.
- `compactRestrict f hf hfc F`, for `hfc : IsClosedEmbedding f`. This is
  `globalRestrict` restricted to compactly supported sections
  (`CompactSupport.submodule`). Since `f` is a closed embedding, the preimage of
  a compact set is compact (`IsClosedEmbedding.isCompact_preimage`). The
  restricted support is a closed subset of it. `compactRestrict_val` records the
  underlying section by `rfl`.
- `globalRestrict_action` and `compactRestrict_action`: restriction intertwines
  the published section representations, both global (`globalRepresentation`) and
  compact (`CompactSections.representation`). Both sides are compared germ by
  germ (`section_ext`). The germ of a translated section is given by the
  published `CompactSectionActions.global_germ_transport`. The two stalk
  transports agree by the published
  `InverseImageStalks.preimageStalkMap_transport` and equivariance of `f`.
- `globalRestrict_naturality` and `compactRestrict_naturality`: restriction is
  natural in `F`, by the published `InverseImageStalks.unit_naturality`.

## Surjectivity

`compactRestrict_surjective`: if `f` is a closed embedding and `X` is locally
profinite (`hX`), every compact section of `res f hf F` is the restriction of a
compact section of `F`. This is the surjectivity of `p_Z` that Renard's proof of
III.3.1 takes from Proposition 2 of II.2.5. The Lean proof is a direct argument.

- `Good b K σ` says that a section `σ` of `F` over an open `K ⊆ X` has, at every
  `z` with `f z ∈ K`, the same germ as `b` after `stalkIso`.
- `good_sub`: if `σ` is good for `b` over `K`, then `σ - a|_K` is good for
  `b - globalRestrict a`. This follows from the germ formula.
- `exists_good`: every `z : Z` has a compact open `K ∋ f z` in `X` with a good
  section. Proof: the germ of `b` at `z`, pulled back by `stalkIso⁻¹`, is the
  germ of some section `τ` of `F` over an open `U ∋ f z`. Two sections over
  `Z` with equal germ at `z` agree on an open `W ∋ z` (`germ_eq`). Since `f` is an
  embedding, `W = f⁻¹(W')` for an open `W'` of `X`. Let `K ∋ f z` be a compact
  open inside `U ∩ W'`. Then `τ|_K` is good: for `f z' ∈ K`, `z'` lies in `W`.
- `exists_restrict_aux` is a finite induction (`Finset.induction_on`) over a
  finite set `t` of points. Its claim: if the support of `b` is covered by the
  sets `f⁻¹(K z)` for `z ∈ t`, and each `K z` is compact open with a good
  section, then `b` is the restriction of a compactly supported section.
  - Empty step: `b` has empty support, so `b = 0 = globalRestrict 0`.
  - Insert step: let `σ` be good over `K = K z₀`. Extend `σ` by zero to a
    compactly supported global section `e` (the published
    `CompactGerms.compactExtension`; `K` is compact, hence closed, in the
    Hausdorff space `X`). Put `b' = b - globalRestrict e`. The germs of `b'` vanish
    on `f⁻¹(K)` and equal those of `b` elsewhere. So the support of `b'` is covered
    by the remaining sets. By `good_sub` the remaining good sections stay good for
    `b'`. The induction hypothesis gives `a'` with restriction `b'`, and `a' + e`
    restricts to `b`.
- `compactRestrict_surjective`: choose `K z` and good sections for every `z`
  (`exists_good`). Cover the compact support of `b` by finitely many of the
  open sets `f⁻¹(K z)` (`IsCompact.elim_nhds_subcover`), then apply
  `exists_restrict_aux`.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French version
dated 9 July 2026, III.3.1, proof of the Proposition, printed p.83 / PDF p.89
("la restriction `p_Z : F_c(X) → F_c(Z)` est surjective (proposition 2 de
II.2.5)"). Registered as
`renard-2026-representations-groupes-reductifs-padiques`. The equivariance and
naturality lemmas and the finite-induction proof of surjectivity are internal
steps of the implemented proof. The source cites II.2.5 for surjectivity instead.
