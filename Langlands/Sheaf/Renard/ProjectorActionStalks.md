# Stalks of Renard's equivariant projector sheaf

This internal helper module supports Renard III.3.2, printed p.85 / PDF p.91: the
sentence that the representation of `H` on the fibre of the induction sheaf at
`o = H1` is isomorphic to `(τ, E)`. The source says this is clear and gives no
argument. The module uses the II.2.5 sheaf construction (printed pp.39–40 /
PDF pp.45–46). Source: David Renard, *Représentations des groupes réductifs
p-adiques*, French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

All declarations have the prefix `Langlands.Sheaf.Renard.ProjectorActionStalks`.
The setting is the published one of `ProjectorActionSheaf`:

- a group `G : Type uG` acting on `X : Type` by `ContinuousConstSMul`;
- `hX : Langlands.Topology.IsLocallyProfinite X`;
- an original compatible test action `M : CompatibleTestAction.{uG, 0, 0} G X`.

`ProjectorActionSheaf.sheaf hX M` is the published reconstructed action sheaf, and
its stalks are the ordinary neighbourhood-colimit stalks of
`CompactSections.ordinary (sheaf hX M).obj`. There is no topology on `G` and no
smoothness assumption.

## Declarations

- `originalGerm hX M x` is the complex-linear map from the original module
  (with its canonical scalars `M.complexModule`) to the stalk at `x`. It sends
  `m` to the germ at `x` of the published original-vector global section
  `ProjectorVectorSheaf.originalSection hX _ ⊤ m`, whose component at a compact
  open `W` is `χ_W · m`. `originalGerm_apply` restates it with `Γgerm` and
  `originalFamily`, by `rfl`.
- `originalGerm_eq_zero_iff`: `originalGerm hX M x m = 0` if and only if some
  compact open `K` contains `x` and satisfies `action hX M.module.obj K m = 0`,
  that is, `χ_K · m = 0`. Forward: `CompactSections.germ_zero_iff` gives an open
  neighbourhood `U` on which the section restricts to zero. The published
  `SmoothProjectorActionSheaf.restrict_originalFamily` identifies that
  restriction with `originalFamily U m`. A compact open `K` with `x ∈ K ⊆ U`
  comes from `compactOpenBasis`, and the component of the zero family at `K` is
  `χ_K · m`. Backward: restrict the section to `K`. Every component `χ_W · m`
  with `W ⊆ K` equals `χ_W · (χ_K · m) = 0` by `action_absorb`.
- `originalGerm_surjective`: every germ is the germ of a section `s` over some
  open `U ∋ x` (Mathlib's `TopCat.Presheaf.exists_germ_eq`). Choose a compact
  open `K` with `x ∈ K ⊆ U`. The published
  `SmoothProjectorActionSheaf.restrict_family_eq_original` says the restriction
  of `s` to `K` is the original-vector section of its own component at `K`. By
  `restrict_originalFamily` this is also the restriction of the global
  original-vector section. Mathlib's `germ_res_apply` and `Γgerm_res_apply` then
  identify the two germs.
- `stalkPull_originalGerm`: if `q⁻¹ • x = x`, the published stalk transport
  `Godement.stalkPull (sheaf hX M).obj q⁻¹ x x _` sends `originalGerm x m` to
  `originalGerm x (M.action q m)`. The proof uses
  `Godement.germ_stalkPull_arrow` on `ActionOpens.sectionArrow q` together with
  `SmoothProjectorActionSheaf.global_originalFamily`.
- `stalkMap_originalGerm`: for a morphism `φ : M ⟶ N` of compatible test
  actions, the ordinary stalk map of `ProjectorActionSheaf.sheafMap hX φ` sends
  `originalGerm x m` to `originalGerm x (φ m)`. The proof uses Mathlib's
  `stalkFunctor_map_germ_apply` and the published
  `ProjectorVectorSheaf.sheafMap_originalSection`.

The module edits no Library file. Its only import is
`Langlands.Sheaf.Renard.SmoothProjectorActionSheaf`.
