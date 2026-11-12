# V 7 and AS 2–AS 5 for the restriction of an apartment class to a Levi subgroup

This internal helper module, in namespace
`Langlands.BruhatTits.SpecialCompact`, proves the apartment axioms V 7 and
AS 2–AS 4 for the restriction of an apartment class to a Levi subgroup. It
also proves the second and third sentences of AS 5 when the Levi subgroup has
the same relative roots as `G`.

## Setting

The setting is that of `leviRestrictedApartmentData` (module
`LeviApartmentRestriction`):

- a smooth connected affine `G` over a field `F`, with `hG` connected
  reductive and a maximal split torus `i : S → G`;
- a locally finite type affine `M`, and `iM : S → M`;
- a closed subgroup `j : M → G` with `iM ≫ j = i` that represents the
  dynamic centralizer of the cocharacter `ζ` of `S`;
- apartment data `D` of `(G, S)`.

`DM` is `leviRestrictedApartmentData hS i iM j hcomp ζ hj hjc hG hi D`, and
`π` is the surjective affine projection `leviApartmentAffineProjection` from
the apartment of `D` onto that of `DM` (module `LeviApartmentProjection`).

## Root criteria

- `eq_zero_of_forall_rootForm_eq_zero`: a vector of `TranslationSpace iM` on
  which all root forms vanish is zero.
- `tmul_mem_rootAnnihilator_levi`: `1 ⊗ ζ` lies in the root annihilator of
  `M`. This is because every relative root of `M` pairs to zero with `ζ`
  (`relativeRoots_centralizer_factor`).
- `leviTranslationProjection_comp_injective`, `finite_range_rootForm_levi`:
  precomposition with the surjective translation projection
  (`leviTranslationProjection_surjective`) is injective, so the Levi root
  forms are finite whenever those of `G` are. The comparison of root forms is
  `rootForm_comp_leviTranslationProjection`.
- `exists_leviRoot_of_comp_linear`: if `ψ ∘ π` has derivative the root form
  of a relative root `α` of `G`, then `α` pairs to zero with `ζ`, by evaluation
  at the image of `1 ⊗ ζ`, which is zero. Hence `α` is a relative root of `M`
  and `ψ` has derivative its Levi root form.
- `mem_affineRoots_levi_iff`, `mem_extendedAffineRoots_levi_iff`: `ψ` is an
  (extended) affine root of `DM` exactly when `ψ ∘ π` is one of `D`. One
  direction is `leviAffineRootPullback_mem_affineRoots` and
  `leviAffineRootPullback_mem_extendedAffineRoots` (module
  `LeviAffineRoots`). The converse uses the previous lemma together with
  `leviAffineRootGroup_subset_mul_iff`, `map_leviAffineRootGroup` and
  `map_leviAffineRootGroupPlus`, which compare the affine root groups of `M`
  and `G`.

## AS 2–AS 4

- `isAffineRootSystem_levi`: a set `ΨM` detected by pullback to an affine
  root system `Ψ` with derivative the roots of `G` is an affine root system
  with derivative the Levi roots, provided every element of `ΨM` has a Levi
  root form as derivative. The proof applies
  `AffineRootSystem.derivativeRoots_eq_of_comp` and
  `AffineRootSystem.isAffineRootSystemWithRankZero_of_comp` (module
  `AffineRootSystemPullback`) along the surjective `π`. Spanning comes from
  `span_eq_top_of_finite_of_forall_eq_zero` with the two lemmas above. Applied
  to `Ψ′` and `Ψ` it gives AS 2 and AS 3.
- `mem_or_two_smul_mem_levi`: AS 4 passes, by the two membership criteria and
  `AffineRootSystem.smul_comp'`.

## AS 5 for a Levi subgroup with the same roots

- `leviApartmentProjection_smul`: `π` intertwines the action of
  `n ∈ N_M(F)` with that of its image in `N_G(F)`
  (`leviRestrictedRootFunctionFamily_smul`).
- `rootAnnihilator_levi_eq`, `leviApartmentAffineProjection_bijective`: if
  `relativeRoots iM = relativeRoots i`, the root annihilators agree and `π`
  is injective (`leviApartmentProjection_eq_iff`), hence bijective.
- `transportedRoots_levi`, `affineConjugation_normalizerAffineEquiv_levi`:
  along the bijective `π`, the affine roots of `DM` are the transport of those
  of `D` (`AffineRootSystem.transportedRoots`,
  `affineFunctionalTransport_mem_transportedRoots_iff`). The action of
  `n ∈ N_M(F)` is the conjugate of the action of its image in `N_G(F)`.
- `range_eq_affineWeylGroup_levi`: with the same roots, if the image of
  `N_G(F)` is `W(Ψ_G)` and the image of `N_M(F)` contains `W(Ψ_M)`, then the
  image of `N_M(F)` is `W(Ψ_M)`. The upper inclusion conjugates through `π`
  (`map_affineWeylGroup_of_transportedRoots_eq`, module
  `AffineWeylTransport`).
- `normalizerPointsMap_surjective_of_isIso`: if `j` is an isomorphism, every
  point of `N_G(F)` comes from `N_M(F)`, by composing with `inv j`.
- `range_eq_extendedAffineWeylGroup_levi`: with the same roots and `j` an
  isomorphism, if the image of `N_G(F)` is `W(Ψ_G)ᵉˣᵗ` and the image of
  `N_M(F)` lies in `W(Ψ_M)ᵉˣᵗ`, then the image of `N_M(F)` is `W(Ψ_M)ᵉˣᵗ`.
  The proof uses `AffineRootSystem.map_extendedAffineWeylGroup` (module
  `AffineExtendedWeylTransport`).

## V 7

- `leviRestricted_isTopologyCompatible`, `isTopologyCompatible_levi`: V 7
  passes to the restricted class. With the point topologies, `j` induces an
  embedding `M(F) → G(F)` (`isEmbedding_rationalPointMap`, module
  `RepresentedSubgroup`). It maps the root groups of `M` onto those of `G`
  (`map_leviRootGroupPoints`) and is therefore an inducing map on them. The
  filtration subgroups of `M` are the preimages of those of `G`
  (`leviRestrictedRootFiltration_eq_comap`), so neighbourhood bases at `1`
  and openness pull back. Algebraic boundedness transfers along the closed
  immersion (`isAlgebraicallyBounded_of_closedImmersion`, module
  `AffineBoundedTransport`). The image of each filtration subgroup is the
  ambient one (`image_leviRestrictedRootFiltration`).

## Provenance

Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), §6.7 and
§6.7.2: the affine roots of `(M, S)` are those obtained through the projection
of apartments, and V 1–V 6 pass to `φ_M` (Lemma 6.7.1). V 7 is in
Definition 6.1.2; AS 2–AS 5 are Axiom 4.1.6. The membership criteria refine
§6.7.2 to an equivalence. The AS 5 transport for a Levi subgroup with the same
roots is derived. It serves the semisimple case of
`LeviApartmentAxiomsInheritanceStatement`, where `M_J = G`. No new source
assertion is used.
