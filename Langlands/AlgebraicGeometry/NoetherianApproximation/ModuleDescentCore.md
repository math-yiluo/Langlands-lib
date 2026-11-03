# A finitely presented submodule sheaf of an affine direct image

Module `Langlands.AlgebraicGeometry.NoetherianApproximation.ModuleDescentCore`, namespace
`Langlands.AlgebraicGeometry.NoetherianApproximation.ModuleDescentCore`, universe `u`. Author:
Worker 1038. This is an internal helper module for the proof of
`FinitePresentationModuleSubalgebraDescentStatement` in
[`ModuleDescentProof`](ModuleDescentProof.md). It asserts no source theorem of its own.

`Γ(F, U)` is Mathlib's group of sections of a module sheaf `F` over an open `U`, a module over
`Γ(Y, U)`. `F.restrict f` is Mathlib's restriction along an open immersion,
`moduleSpecΓFunctor` the global-sections functor on a spectrum, `tilde` the associated sheaf
of a module, and `F.fromTildeΓ : tilde Γ(F) ⟶ F` the counit of their adjunction.

## Main result

```lean
theorem exists_isFinitePresentation_pullback_iso (hfs : ∀ i, IsAffineHom (hV i).fromSpec)
    [∀ i, IsNoetherianRing Γ(Y, V i)] (hcov : ∀ y : Y, ∃ i, y ∈ V i)
    (hcross : CrossCondition q M V g) (hrel : ∀ k, RelationCondition q M V g k) :
    ∃ G : Y.Modules, G.IsFinitePresentation ∧
      Nonempty ((Scheme.Modules.pullback q).obj G ≅ M)
```

The data are an affine morphism `q : X ⟶ Y`, a quasi-coherent `M : X.Modules`, a finite family
`V : ι → Y.Opens` (`ι : Type u`, `[Fintype ι]`) of affine opens covering `Y` (`hcov`) whose
inclusions `(hV i).fromSpec` are affine morphisms (`hfs`) and whose coordinate rings are
noetherian, and finitely many sections `g i : Fin (n i) → Γ(directImage q M, V i)` of the direct
image `directImage q M := (Scheme.Modules.pushforward q).obj M`. Note that
`Γ(directImage q M, V i)` is `Γ(M, q ⁻¹ᵁ V i)`, with `Γ(Y, V i)` acting through `q.app`.

The two hypotheses are:

- `RelationCondition q M V g k`: there are relation vectors `ρ : Fin m → Fin (n k) → Γ(Y, V k)`
  with `∑ l, ρ a l • g k l = 0` for every `a`, the sections `g k` generate `Γ(M, q ⁻¹ᵁ V k)`
  over `Γ(X, q ⁻¹ᵁ V k)`, and every relation `c` among the `g k` over `Γ(X, q ⁻¹ᵁ V k)` lies in
  the span of the vectors `q.app (V k) (ρ a ·)`;
- `CrossCondition q M V g`: for all `i k` and every point `y` of `V i ⊓ V k` there is an open
  `D ∋ y` inside `V i ⊓ V k` on which every restricted `g k l` lies in the `Γ(Y, D)`-span of
  the restricted `g i`.

So `M` is the pullback of a locally finitely presented module on `Y`. Only coefficients from
`Y` enter the hypotheses: the sections themselves are sections of `M` on `X`.

## Construction

For each `i`, write `fᵢ := (hV i).fromSpec : Spec Γ(Y, V i) ⟶ Y` and `F := directImage q M`,
which is quasi-coherent by the Library's `isQuasicoherent_pushforward`.

1. `chart F hV : Γ(F, V) →ₗ[Γ(Y, V)] moduleSpecΓFunctor.obj (F.restrict hV.fromSpec)` is
   restriction to `hV.fromSpec ''ᵁ ⊤`, which equals `V` (`image_fromSpec_top`); it is linear
   by the Library identity `appIso_inv_map_ΓSpecIso_inv` and bijective (`chart_bijective`).
2. `spanSub i` is the `Γ(Y, V i)`-span of `g i`, and `chartSub i` its image under `chart`.
3. For a quasi-coherent `A` on `Spec R` and a submodule `Q` of its global sections,
   `quotientMap A Q : A ⟶ tilde (Γ(A) ⧸ Q)` is the inverse of the counit followed by `tilde` of
   the quotient map. On global sections it is the quotient map followed by `tilde.toOpen`
   (`quotientMap_app_top`, using Mathlib's `toOpen_fromTildeΓ_app` and `tilde.toOpen_map_app`),
   so a global section is killed exactly when it lies in `Q`
   (`quotientMap_app_top_eq_zero_iff`).
4. `component i : F ⟶ (pushforward fᵢ).obj (quotientSheaf ...)` is the unit of the
   restriction–pushforward adjunction of `fᵢ` followed by the pushforward of `quotientMap`.
   `total` is `biproduct.lift component` into the finite biproduct, and
   `descended := kernel total` with inclusion `descendedι`.

## Sections of the descended module

- `component_self_app_eq_zero_iff`: over `V i`, `component i` kills `x` exactly when
  `x ∈ spanSub i`. The restriction of the target from `fᵢ ⁻¹ᵁ V i` to `⊤` is bijective, and the
  two restrictions of `x` compose to `chart x`.
- `component_app_eq_zero_of_mem`: under the cross condition for `(i, k)`, `component i` kills
  every element of `spanSub k` over `V k`. The target's sections over `V k` and over
  `V k ⊓ V i` agree (equal preimages under `fᵢ`); over each `D` from the cross condition the
  restricted section lies in the span of the restricted `g i`, which `component i` kills by
  linearity and the previous lemma; the Library's `eq_of_forall_mem` concludes.
- `total_app_eq_zero_iff`: the total map kills a section exactly when every component does
  (`biproduct_app_eq_zero`, from `IsBilimit.total`).
- Hence `descendedι_app_mem` and `exists_descendedι_app_eq` identify the sections of
  `descended` over `V k` with `spanSub k`, using the Library's kernel-section lemmas
  `kernel_ι_app_injective`, `app_kernel_ι_app` and `exists_kernel_ι_app_eq`.
- `isQuasicoherent_descended`: kernels of maps of quasi-coherent modules are quasi-coherent
  (`isQuasicoherent_kernel`); the targets are pushforwards along the affine `fᵢ` of associated
  sheaves; `isQuasicoherent_biproduct` proves that finite biproducts of quasi-coherent modules
  are quasi-coherent, restricting to affine opens and applying the Library's
  `isQuasicoherent_biproduct_spec`.

## Finite presentation

`isFinitePresentation_descended`: lifts of the `g k` to `descended` span its sections over
`V k` (`span_descended_eq_top`), so these sections, and through `chart` the global sections of
its restriction to `Spec Γ(Y, V k)`, form a finite and hence finitely presented module over
the noetherian ring `Γ(Y, V k)`. The Library's `exists_presentation_tilde`, transported along
the counit isomorphism (quasi-coherence on a spectrum), gives a finite presentation of the
restriction along `fₖ`; `exists_presentation_opensRange` moves it to `V k`, and
`isFinitePresentation_of_forall_exists_presentation` assembles local finite presentation.

## The comparison isomorphism

- `comparison : (pullback q).obj descended ⟶ M` is the adjoint of `descendedι`;
  `comparison_app_sectionPullback` says it sends the pulled-back section of `t` to
  `descendedι t` (from `Adjunction.homEquiv_unit`).
- `bijective_of_relations` (pure algebra, section `Algebra`): for `φ : B →+* R`, a map
  `Ψ : R ⊗_B Q ⟶ P` with `Ψ (r ⊗ t l) = r • p l`, generators `t` of `Q`, relations `ρ` among
  them over `B`, generators `p` of `P` over `R`, and every relation among the `p` in the
  `R`-span of `φ ρ`, is bijective. Injectivity writes every tensor as `∑ c l ⊗ t l`
  (`exists_eq_sum_tmul`) and rewrites a relation through `tmul_eq_smul_one_tmul`.
- `bijective_comparison_app`: on `q ⁻¹ᵁ V k`, the comparison composed with the Library's
  bijective `pullbackTensorMap` (affine opens, quasi-coherent `descended`) is such a `Ψ`, with
  `t` the lifts of `g k`, `p` the `g k` themselves and `ρ` from the relation condition.
- `isIso_of_bijective_app_top`: a map of quasi-coherent sheaves on a spectrum that is bijective
  on global sections is an isomorphism (naturality of `fromTildeΓNatTrans`).
- `isIso_comparison`: the Library's `isIso_of_affineOpenPullbacks`, with the affine open
  neighbourhoods `q ⁻¹ᵁ V k` (affine as `q` is affine), `restrictFunctorIsoPullback`, and the
  previous two lemmas.

## Finite presentation of affine sections

- `finitePresentation_moduleSpecΓ`: a locally finitely presented sheaf on `Spec R` has finitely
  presented global sections. Each point has a basic open on which, through `chart` and the
  Library's `presentationRestrictOfFac` and `finitePresentation_moduleSpecΓFunctor_of_presentation`,
  the sections of the associated sheaf of the global sections are finitely presented; these
  basic opens give a spanning set, and Mathlib's
  `Module.FinitePresentation.of_localizationSpan'` applies to the localization maps
  `tilde.toOpen`.
- `finitePresentation_sections_of_isAffineOpen`: over an affine open `U` of any scheme,
  `Γ(M, U)` is finitely presented over `Γ(X, U)` for locally finitely presented `M` (restrict
  along `hU.fromSpec`, using `isFinitePresentation_pullback` and `chart`).

## Provenance

Internal. The construction is a Lean realization of the Zariski-gluing step in the first proof
of Stacks Project, Limits of Schemes, Lemma 01ZR (`limits.tex` at commit `a04446e5`, lines
2582–2605, registered as `stacks-limits-of-schemes-a04446e5`): the glued module is realized as a
subsheaf of the direct image cut out by local conditions, which needs no cocycle verification.
`finitePresentation_moduleSpecΓ` is the standard fact that finite presentation is local on an
affine scheme, proved here through Mathlib's localization-span criterion.
