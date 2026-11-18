# Proof: spreading out a factorization from the local scheme at a point

Worker 5600.

`Langlands.AlgebraicGeometry.specStalkFactorizationSpreading :
SpecStalkFactorizationSpreadingStatement.{u}` proves the Library statement
`Langlands.AlgebraicGeometry.SpecStalkFactorizationSpreadingStatement` (module
`Langlands.AlgebraicGeometry.SpecStalkFactorizationSpreadingStatement`) in every universe `u`,
with no additional hypotheses. The module imports only Mathlib
(`Mathlib.AlgebraicGeometry.AffineTransitionLimit`, `Mathlib.AlgebraicGeometry.Stalk`) and the
statement module. It uses no `sorry` and no new axioms. The whole file sets
`backward.isDefEq.respectTransparency false`, as Mathlib's own `AffineTransitionLimit.lean` does
for its lemmas. Without this option `simp` cannot reduce `pullback.map … ≫ pullback.fst` in
`Scheme`, and Lean cannot find the base-change instances for quasi-compactness and
quasi-separatedness.

## Statement proved

Let `p : X ⟶ S` be quasi-compact and quasi-separated, let `k : K ⟶ X` be locally of finite
presentation, and let `s ∈ S`. Suppose `y : X ×_S Spec 𝒪_{S,s} ⟶ K` satisfies
`y ≫ k = pullback.fst`. Then there are an open `U ∋ s` and a morphism
`X ×_S U ⟶ K` whose composite with `k` is `pullback.fst p U.ι`.

## Route

The proof follows the derivation in the statement's Markdown: write `Spec 𝒪_{S,s}` as the
limit of the affine open neighbourhoods of `s`, pull this limit back along `p`, and apply
Mathlib's limit theorem for morphisms locally of finite presentation. All auxiliary
declarations are in the namespace
`Langlands.AlgebraicGeometry.SpecStalkFactorizationSpreading`.

### 1. Index category and `Spec 𝒪_{S,s}` as a limit

- `AffineNhds s` is the subtype `{U : S.Opens // s ∈ U ∧ IsAffineOpen U}`, a preorder ordered
  by inclusion. It is nonempty and codirected (`IsCodirectedOrder`): any two members contain an
  affine open neighbourhood of `s`, found with Mathlib's `exists_isAffineOpen_mem_and_subset`.
  Hence it is a cofiltered category.
- `incl s : AffineNhds s ⥤ OpenNhds s` is the inclusion. It is an initial functor, by
  `Monotone.initial_functor_iff`, because every open neighbourhood of `s` contains an affine one.
- `sectionsDiagram s` is `U ↦ Γ(S, U)` on `(AffineNhds s)ᵒᵖ`. `germCocone s` is the colimit
  cocone of the stalk `𝒪_{S,s}` restricted along `(incl s).op`. `isColimitGermCocone s` shows
  that it is still a colimit, since `(incl s).op` is final
  (`Functor.Final.isColimitWhiskerEquiv`).
- `specDiagram s : AffineNhds s ⥤ Scheme` is `U ↦ Spec Γ(S, U)`, and `specCone s` is the image
  of the germ cocone under `Spec`. `isLimitSpecCone s` shows that it is a limit cone with apex
  `Spec 𝒪_{S,s}`, because `Scheme.Spec` preserves limits (`isLimitOfPreserves`).
- `specToBase s U = U.2.2.fromSpec : Spec Γ(S, U) ⟶ S`. The lemma
  `specDiagram_map_specToBase` says that these maps commute with the transition maps
  (Mathlib's `IsAffineOpen.map_fromSpec`). The lemma `specCone_π_specToBase` says that
  `Spec 𝒪_{S,s} ⟶ Spec Γ(S, U) ⟶ S` is `S.fromSpecStalk s` (Mathlib's
  `IsAffineOpen.fromSpecStalk_eq_fromSpecStalk`).

### 2. Pulling the limit back along `p`

- `pullbackDiagram s p : AffineNhds s ⥤ Scheme` is `U ↦ X ×_S Spec Γ(S, U)`. Its maps are the
  `pullback.map`s induced by the transition maps of `specDiagram s`.
- `pullbackToSpec s p` and `pullbackToX s p` are the natural transformations given by the
  second projections to `specDiagram s` and by the first projections to the constant diagram `X`.
- `pullbackCone s p` is the cone with apex `X ×_S Spec 𝒪_{S,s}` and legs the `pullback.map`s
  induced by the legs of `specCone s`. The lemmas `pullbackCone_π_fst` and `pullbackCone_π_snd`
  compute its legs followed by the two projections.
- `isPullback_pullbackCone`: for each `U` the square with corners
  `X ×_S Spec 𝒪_{S,s}`, `Spec 𝒪_{S,s}`, `X ×_S Spec Γ(S, U)` and `Spec Γ(S, U)` is a pullback.
  The proof uses pullback pasting (`IsPullback.of_right`): the outer rectangle over
  `p : X ⟶ S` is the pullback square of `p` and `S.fromSpecStalk s`, by `specCone_π_specToBase`.
- `isLimitPullbackCone s p`: `pullbackCone s p` is a limit cone. This is Mathlib's
  `isLimitOfIsPullbackOfIsConnected`. The index category is connected because it is
  cofiltered, and every leg square is a pullback by `isPullback_pullbackCone`.
- `isPullback_pullbackDiagram_map`: in the same way, each transition square over the map
  `Spec Γ(S, U) ⟶ Spec Γ(S, V)` is a pullback (lemmas `pullbackDiagram_map_fst`,
  `pullbackDiagram_map_snd`). The transition map between affine schemes is affine, so each
  transition map of `pullbackDiagram s p` is affine (instance `IsAffineHom`, via
  `MorphismProperty.of_isPullback`).

### 3. The main theorem

`specStalkFactorizationSpreading` introduces the data and the given factorization `y`, `hy`.

- Each `X ×_S Spec Γ(S, U)` is quasi-compact and quasi-separated. Its projection to the affine
  scheme `Spec Γ(S, U)` is a base change of `p`, hence quasi-compact and quasi-separated
  (`QuasiCompact.compactSpace_of_compactSpace`, `quasiSeparatedSpace_of_quasiSeparated`).
- Mathlib's `Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation` is applied to the
  cofiltered diagram `pullbackDiagram s p` over `X` (via `pullbackToX s p`), to the morphism `k`,
  to the limit cone `pullbackCone s p` and to `a = y`. Its compatibility hypothesis
  `(pullbackCone s p).π ≫ pullbackToX s p = const (y ≫ k)` follows from `pullbackCone_π_fst`
  and `hy`. It returns some `U : AffineNhds s` and `g : X ×_S Spec Γ(S, U) ⟶ K` with
  `g ≫ k = pullback.fst p (specToBase s U)`.
- The witness is the open `U.1` with `s ∈ U.1`, and the morphism
  `pullback.lift (pullback.fst p U.1.ι) (pullback.snd p U.1.ι ≫ U.2.2.isoSpec.hom) _ ≫ g`.
  This lift `X ×_S U ⟶ X ×_S Spec Γ(S, U)` is well defined because
  `U.2.2.isoSpec.hom ≫ U.2.2.fromSpec = U.1.ι` (`IsAffineOpen.isoSpec_hom_fromSpec`). Its
  composite with `k` is `pullback.fst p U.1.ι`, by `hg` and `pullback.lift_fst`.

The proof does not use the uniqueness or compatibility part of the Mathlib theorem. This
matches the statement, which asks only for existence.

## Sources

The route is the one described in the statement's Markdown: EGA IV₃ (8.8.2) (i) and Stacks
tag 01ZC (3), applied to the limit `Spec 𝒪_{S,s} = lim U` (Stacks tag 0EY3). The
finite-presentation limit argument itself is Mathlib's
`AlgebraicGeometry.Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation` in
`Mathlib/AlgebraicGeometry/AffineTransitionLimit.lean`.
