# Gluing morphisms of module sheaves from a basis of opens

Fix a scheme `Y : Scheme.{u}` and a predicate `P : Y.Opens → Prop` on its opens. The
`P`-opens form a *basis* when they satisfy the hypothesis

`hP : ∀ (y : Y) (U : Y.Opens), y ∈ U → ∃ V, P V ∧ y ∈ V ∧ V ≤ U`,

that is, every open neighbourhood of every point contains a `P`-open neighbourhood of
that point. For a module `N : Y.Modules`, `Γ(N, V)` is Mathlib's group of sections over
`V`, a module over `Γ(Y, V)`. `N.presheaf.map (homOfLE h).op` is restriction along
`h : W ≤ V`.

This module shows that a morphism of module sheaves is determined by its values on a
basis, and that compatible linear maps on a basis come from a morphism. All
declarations are in the namespace `Langlands.Scheme.Modules.BasisHomGluing`.

## Uniqueness

- `le_iSup_basicSub hP O`: every open `O` is covered by the `P`-opens contained in
  it. These are indexed by the subtype `BasicSub P O = {W // P W ∧ W ≤ O}`.
- `eq_of_basis hP s t h`: two sections `s t : Γ(N, O)` whose restrictions to every
  `P`-open `W ≤ O` agree are equal. This is Mathlib's
  `TopCat.Sheaf.eq_of_locally_eq'` for the cover above.
- `hom_ext_of_basis hP f g h`: two morphisms `f g : N ⟶ M` with `f.app V = g.app V`
  for every `P`-open `V` are equal. The proof applies `eq_of_basis` to each section,
  together with the naturality of `f` and `g` under restriction.

## Existence

The data are `M N : Y.Modules`, a family of `Γ(Y, V)`-linear maps
`θ V hV : Γ(N, V) →ₗ[Γ(Y, V)] Γ(M, V)`, one for each `P`-open `V`, and the
compatibility hypothesis

`hθ : ∀ V V' hV hV' (h : V' ≤ V) s, (θ V hV s)|_{V'} = θ V' hV' (s|_{V'})`,

which is required only for pairs of `P`-opens.

- `glue hP θ hθ O x`: for an arbitrary open `O` and `x : Γ(N, O)`, this is the
  section of `M` over `O` obtained by gluing the sections `θ W (x|_W)` over the cover
  of `O` by `P`-opens `W ≤ O` (Mathlib's `TopCat.Sheaf.existsUnique_gluing'`). The
  gluing condition on `W ⊓ W'` is checked with `eq_of_basis`. On every `P`-open
  `Z ≤ W ⊓ W'`, both sides restrict to `θ Z (x|_Z)` by `hθ`. This is needed because
  `W ⊓ W'` itself need not be a `P`-open.
- `glue_spec`: for a `P`-open `W ≤ O`, `(glue O x)|_W = θ W (x|_W)`.
- `glue_add`, `glue_smul` and `glue_map`: `glue O` is additive and
  `Γ(Y, O)`-linear, and it commutes with restriction. Each is proved with
  `eq_of_basis` and `glue_spec`. `glue_smul` also uses Mathlib's
  `Scheme.Modules.map_smul` and the linearity of `θ W`.
- `presheafHom` and `hom hP θ hθ : N ⟶ M`: the resulting morphism of abelian
  presheaves, and then of module sheaves via `PresheafOfModules.homMk`. These follow
  the published `OpenCoverHomGluing.LocalFamily.presheafHom` and `LocalFamily.hom`.
- `hom_app_apply`: `(hom hP θ hθ).app O x = glue hP θ hθ O x` (definitional).
- `hom_app_basis`: for a `P`-open `V`, `(hom hP θ hθ).app V s = θ V hV s`.
- `exists_hom_of_basis`: there is a morphism `φ : N ⟶ M` with
  `φ.app V s = θ V hV s` for every `P`-open `V` and every `s : Γ(N, V)`.

## Provenance and scope

This is an internal helper. It formalizes the standard fact that a morphism of sheaves
is determined by, and can be glued from, compatible maps on a basis of the topology,
for sheaves of modules over the structure sheaf. Compare Stacks Project, Lemma 6.30.13
(Tag 009U): restricting `𝒪`-modules to the members of a basis is an equivalence of
categories. `hom_ext_of_basis` is the faithfulness of that restriction and
`exists_hom_of_basis` its fullness, with a morphism on the basis given as compatible
linear maps `θ`. The Lean proof does not go through that equivalence. It adapts the published
`Langlands.Scheme.Modules.OpenCoverHomGluing` construction (module
`Modules/OpenCoverHomGluing.lean`), whose helper lemmas `sheafAb`, `map_map_eq` and
`hom_map_app` it reuses. There, the maps are given on all opens inside the members of a
cover. Here they are given only on the basic opens themselves. It also uses pinned
Mathlib (`Mathlib/Topology/Sheaves/SheafCondition/UniqueGluing.lean` and
`Mathlib/AlgebraicGeometry/Modules/Sheaf.lean`, commit
`5ed2965256430c3649e86755f9576b54eca72435`). It makes no claim about quasi-coherence,
about isomorphisms, or about uniqueness of `hom` beyond `hom_ext_of_basis`.
