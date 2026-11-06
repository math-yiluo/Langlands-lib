# Proper coherent formal existence from the presheaf existence theorem

Author: Worker 1405.

This module is `Langlands.AlgebraicGeometry.Modules.ProperFormalCoherentExistenceOfFLT`.
All declarations are in the namespace
`Langlands.AlgebraicGeometry.Modules.ProperFormalCoherentExistenceOfFLT`.

## Main result

`properFormalCoherentExistence_of_flt (hflt : …) : ProperFormalCoherentExistenceStatement.{u}`.

The target `ProperFormalCoherentExistenceStatement` (Library module
`Langlands.AlgebraicGeometry.Modules.ProperFormalCoherentExistenceStatement`)
says: for a complete local noetherian ring `R` with maximal ideal `𝔪`, a
proper `f : X ⟶ Spec R` and a formal module system `F` over the
`𝔪`-adic thickenings `X_n` with every `F_n` locally finitely presented, there
are a locally finitely presented `M : X.Modules` and a comparison of formal
module systems from the restrictions `p_n^* M` to `F`: isomorphisms
`p_n^* M ≅ F_n` commuting with all transitions.

The hypothesis `hflt` is the statement of the theorem
`AlgebraicGeometry.OModulePresheaf.exists_isCoherent_forall_ker_eq_pow_smul_top_of_isProper_of_isAdicComplete`
of the Anthropic FLT source, written as a proposition (its named hypotheses
become implications): for a noetherian ring `A` complete for an ideal
`I`, a proper `q : P ⟶ Spec A`, coherent quasi-coherent module presheaves
`F k` on `P` and morphisms on affine opens `φ k : F (k+1) → F k` that are
surjective with kernel `I^(k+1) • ⊤`, there are a coherent quasi-coherent
`G` and morphisms on affine opens `ψ k : G → F k` that are surjective with
kernel `I^(k+1) • ⊤` and satisfy `φ k ∘ ψ (k+1) = ψ k`. It is stated with the
Library definitions `OModulePresheaf`, `OModulePresheaf.IsCoherent`,
`OModulePresheaf.IsQuasicoherent` and `OModulePresheaf.AffHom` (ported FLT
definitions in `Langlands.AnthropicFLT.Definitions`). The theorem does not
prove `hflt`; the port of the FLT proof supplies it.

## Purpose and provenance

This is the input bridge and the comparison of the proof task `20cb772c`,
assembled into one conditional theorem so that it does not depend on the
port of the FLT theorem. The statement of `hflt` is taken from
`Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isProper_of_isAdicComplete.lean`
(registered source `anthropic-flt-complete-lean-source-6e837e75`, commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`, 32 lines, SHA-256
`ee3200dcb57a617b616527cba63c9efc5474dc7a491dda5bb61dea41f8b05a12`; Apache 2.0,
see [LICENSE](../../../licenses/Anthropic-FLT/LICENSE),
[NOTICE](../../../licenses/Anthropic-FLT/NOTICE) and
[ATTRIBUTION.md](../../../licenses/Anthropic-FLT/ATTRIBUTION.md)). All
constructions and proofs in this module were written for this development.

## Proof of the main result

1. `X` is locally noetherian (`LocallyOfFiniteType.isLocallyNoetherian`,
   since `f` is proper and `R` is noetherian).
2. Apply `hflt` with `I = 𝔪` to the presheaves `presheaf F n` and the maps
   `phi F n` of `FormalModuleSystemPresheaves`; their hypotheses are
   `isCoherent_presheaf`, `isQuasicoherent_presheaf` and
   `surjective_and_ker_phi`. This gives `G` and `ψ`.
3. `CoherentPresheafRealization.exists_modules_sectionsEquiv` turns `G` into
   a locally finitely presented `M : X.Modules` with linear equivalences
   `e U : Γ(M, U) ≃ G(U)` on affine opens, compatible with restriction (`he`).
4. The comparison has components `asIso (comp ψ he n)` (`isIso_comp`) and
   squares `comp_commutes`.

## Construction of the comparison

Section `Comparison` fixes `F`, `G`, `ψ`, `M`, `e` and `he`.

- `thetaLinear F ψ M e n V hV : Γ(M, V) →ₗ Γ(p_n_* F_n, V)` is
  `s ↦ ψ_n (e_V s)` on an affine open `V`; it is `Γ(X, V)`-linear because
  `ψ_n` is, and `thetaLinear_map` shows compatibility with restriction from
  `he` and `AffHom.naturality_apply`.
- `theta ψ he n : M ⟶ p_n_* F_n` glues these maps over the basis of affine
  opens (`BasisHomGluing.hom` with `basis_affineOpens`).
- `comp ψ he n : p_n^* M ⟶ F_n` is the adjoint of `theta` under
  `pullbackPushforwardAdjunction`. By `homEquiv_app_apply`, it sends the
  pulled-back section `sectionPullback p_n M U m` to `ψ_n (e_U m)` for affine
  `U` (`comp_app_sectionPullback`).

## Proof that the comparison is an isomorphism

- `isIso_of_bijective_of_basis`: a morphism of module sheaves that is bijective
  on sections over every member of a basis of opens is an isomorphism. The
  inverse is glued from the inverse linear equivalences with
  `BasisHomGluing.hom`, and both composites are the identity by
  `BasisHomGluing.hom_ext_of_basis`.
- `basis_preimage_affineOpens`: for a closed immersion `g : Z ⟶ Y`, the inverse
  images of affine opens of `Y` form a basis of `Z` (every open of `Z` is the
  inverse image of an open of `Y`).
- `comp_app_bijective`: for affine `U`, put `σ : Γ(X, U) → Γ(X_n, p_n⁻¹ U)`;
  it is surjective since `p_n` is a closed immersion
  (`Scheme.Hom.app_surjective`). Since `M` is quasi-coherent,
  `pullbackTensorMap_bijective` identifies `Γ(p_n^* M, p_n⁻¹ U)` with
  `Γ(X_n, p_n⁻¹ U) ⊗ Γ(M, U)`, and `comp` sends `1 ⊗ m` to `ψ_n (e_U m)`. That
  map is surjective because `ψ_n` and `e_U` are. If `ψ_n (e_U m) = 0` then
  `e_U m ∈ I^(n+1) • ⊤`, so `e_U m ∈ J • ⊤` for the image `J` of `I^(n+1)` in
  `Γ(X, U)`. Then `m ∈ J • ⊤` (transport through `e_U`), and `J ≤ ker σ`
  because the structure map of `X_n` kills `I^(n+1)`
  (`algebraMap_adicProjection_eq_zero`). So `m ∈ ker σ • ⊤`, and
  `FormalModuleSystemPresheaves.bijective_of_one_tmul` applies.
- `isIso_comp` combines the three.

## Proof of compatibility with transitions

`comp_commutes` states
`t_n^*(comp_(n+1)) ≫ (F.transition n).hom = (restriction transition) ≫ comp_n`,
where the restriction transition is the one of
`FormalModuleSystem.ofModule f I M`. Move the inverse of the restriction
transition to the left (`Iso.inv_comp_eq`). Two morphisms out of `p_n^* M`
agree when they agree on pulled-back sections `sectionPullback p_n M U m`
for affine `U` (`pullback_hom_ext_of_basis`, via the adjunction and
`BasisHomGluing.hom_ext_of_basis`). On such a section:

- `ofModule_transition_inv_app`: the inverse restriction transition sends it
  to the restriction of the pullback along `t_n` of
  `sectionPullback p_(n+1) M U m`. This is the general lemma
  `pullbackComp_trans_congr_inv_app` for the isomorphism
  `a^* b^* M ≅ (a ≫ b)^* M ≅ c^* M`, proved from the Library lemmas
  `pullbackCongr_inv_sectionPullbackLE` and
  `pullbackComp_inv_sectionPullbackLE`.
- `pullback_map_sectionPullbackLE`: `t_n^*(comp_(n+1))` acts on it through
  `comp_(n+1)`, which gives `ψ_(n+1)(e_U m)` by `comp_app_sectionPullback`.
- The result is `transitionSections F n U (ψ_(n+1)(e_U m)) =
  (phi F n)(ψ_(n+1)(e_U m))`, which equals `ψ_n (e_U m)` by the compatibility
  in `hflt`, and that is `comp_n` of the section.

## General lemmas

`appLinear`, `isIso_of_bijective_of_basis`, `homEquiv_app_apply`,
`pullback_hom_ext_of_basis`, `pullback_map_sectionPullbackLE`,
`pullbackComp_trans_congr_inv_app`, `basis_affineOpens` and
`basis_preimage_affineOpens` (section `General`) do not mention formal module
systems.
