# Pullback and tilde comparisons for realizations of affine test systems

Lean module: `Langlands.AlgebraicGeometry.Modules.AffineTestComparison`.

It builds on `Langlands.AlgebraicGeometry.Modules.AffineTestRealization`, where an
`AffineTestSystem S` (an `R`-module `E.obj a` for every affine test `a : Spec R ⟶ S`, with
coherent coefficient-extension isomorphisms `E.ext h : A ⊗[R] E.obj a ≃ E.obj b`) is realized
as a quasi-coherent sheaf `E.toModules` on `S`. This module compares realizations along
morphisms of schemes and produces, for every affine test `a : Spec R ⟶ S`, a canonical
isomorphism `a^* E.toModules ≅ (E.obj a)^~`. These isomorphisms are proved compatible with
coefficient extension along every ring map `R → A`.

## Transport and coefficient extension

- `transport (h : a = a') : E.obj a ≃ₗ[R] E.obj a'` transports a module along an equality of
  tests. `map_transport`, `transport_map` and `transport_transport` describe how it interacts with
  `E.map` and with itself.
- `map_bijective_of_isIso`: coefficient extension along a ring isomorphism is bijective.
- `map_map`: `E.map f' (E.map f x) = E.map (f ≫ f') x`.
- `ext_one_tmul`: for any `R`-algebra structure on `A`,
  `E.ext h (1 ⊗ x) = E.map (algebraMap R A) h x`. Note that `E.map` uses the algebra structure
  `RingHom.toAlgebra`, which agrees only propositionally with an arbitrary given instance.

## Pullback systems and their morphisms

- `pullback g : AffineTestSystem Y`, for `g : Y ⟶ S`, has `obj c = E.obj (c ≫ g)`.
- `Hom E F g`, for systems `E` on `S` and `F` on `Y`, consists of `R`-linear maps
  `app c : E.obj (c ≫ g) → F.obj c` for all tests `c : Spec R ⟶ Y`. They must commute with
  coefficient extension (`naturality`).
- `Hom.comp ν μ : Hom E G (k ≫ g)` composes morphisms over `g` and `k`. `toPullback g` is the
  tautological morphism `E → E.pullback g`. `pullbackComp g k` is the identification
  `E.pullback g → E.pullback (k ≫ g)` over `k`, with
  `toPullback_comp_pullbackComp : (toPullback g).comp (pullbackComp g k) = toPullback (k ≫ g)`.

## The comparison morphism

Fix `ν : Hom E F g`.

- `chartMap ν hU hV h` (for affine opens `U ⊆ S`, `V ⊆ Y` with `V ≤ g⁻¹ U`) extends coefficients
  along `g.appLE U V h : Γ(S, U) → Γ(Y, V)` and then applies `ν`. The lemmas `res_chartMap` and
  `chartMap_res` show it is compatible with restriction on both sides. `family` packages these
  values into a compatible family over the affine opens of `g⁻¹ U`.
- `theta`, `psi`: on each affine open `U` of `S`, `thetaFun` sends a section `m` of
  `E.toModules` to the section of `F.toModules` over `g⁻¹ U` built from `family`. These maps are
  glued (`BasisHomGluing.hom`) into `psi ν : E.toModules ⟶ g_* F.toModules`.
- `comparison ν : g^* E.toModules ⟶ F.toModules` is the adjoint of `psi ν`.
- `sectionsEquiv_comparison_app`: on a pulled-back section `sectionPullbackLE g _ h m` over an
  affine `V ≤ g⁻¹ U`, the comparison is `chartMap ν hU hV h (E.sectionsEquiv hU m)` under the
  section identifications of the two realizations.
- `isIso_comparison`: if every `ν.app c` is bijective, `comparison ν` is an isomorphism.
  On every affine `V ≤ g⁻¹ U` with `U` affine, the map
  `Γ(Y, V) ⊗_{Γ(S, U)} Γ(E.toModules, U) → Γ(g^* E.toModules, V)` is bijective
  (`pullbackTensorMap_bijective`, as `E.toModules` is quasi-coherent). Composed with the
  comparison it is `ν ∘ E.ext ∘ (id ⊗ sectionsEquiv)`, which is bijective. Such `V` form a basis,
  so `isIso_of_bijective_of_basis` applies.
- `pullback_hom_ext_local`: morphisms out of `h^* M` agree if, around every point of `h⁻¹ U` for
  every affine `U`, they agree on the restricted pulled-back sections of sections over `U`.
- `comparison_comp`: `comparison (ν.comp μ) = (pullbackComp k g)⁻¹ ≫ k^*(comparison ν) ≫
  comparison μ`. Both sides are evaluated on pulled-back sections over small affine opens
  (`pullbackComp_inv_sectionPullbackLE`, `pullback_map_sectionPullbackLE`), using `chartMap_comp`
  and `Scheme.Hom.appLE_comp_appLE`.

## The tilde comparison and the frames

For an affine test `a : Spec R ⟶ S`:

- `topLinear a : E.obj a →ₗ[R] Γ((E.pullback a).toModules, ⊤)` maps `x` to the global section
  corresponding to `E.map (ΓSpecIso R).inv x`. Here `⊤` is affine, with chart
  `Spec Γ(Spec R, ⊤) ⟶ Spec R` (`IsAffineOpen.fromSpec_top`). The map is bijective
  (`topLinear_bijective`).
- `tildeComparison a : (E.obj a)^~ ⟶ (E.pullback a).toModules` is its adjoint under the
  tilde–Γ adjunction. It is an isomorphism (`isIso_tildeComparison`): it factors as
  `tilde.map (topLinear a)` followed by the counit `fromTildeΓ`, which is an isomorphism
  because the realization is quasi-coherent. `tildeComparison_app_toOpen` gives its value on
  `tilde.toOpen _ ⊤ x`.
- **`frame a : a^* E.toModules ≅ (E.obj a)^~`** is
  `comparison (toPullback a)` followed by the inverse of `tildeComparison a`.

## Coherence

Let `A` be an `R`-algebra, `p = Spec.map (algebraMap R A) : Spec A ⟶ Spec R`, and `b : Spec A ⟶ S`
with `h : p ≫ a = b`. `extHom a h` is `E.ext h : A ⊗[R] E.obj a ≃ E.obj b` as a morphism in
`ModuleCat A`.

- `pullback_tildeComparison_comp`:
  `p^*(tildeComparison a) ≫ comparison (pullbackComp a p) =
    (tildePullbackAlgebraIso R A (E.obj a)).hom ≫ tilde.map (extHom a rfl) ≫ tildeComparison (p ≫ a)`.
  By `tildePullback_hom_ext` it suffices to compare the adjoints on the global generators
  `tilde.toOpen _ ⊤ m` (`tildeSquare_left`, `tildeSquare_right`). Both values are then read on
  affine opens (`tildeSquare_sections`), using `tildePullbackAlgebraIso_adjoint_toOpen`,
  `ext_one_tmul` and the naturality of `ΓSpecIso` (`ringHom_top_eq`).
- **`frame_hom_eq`** (coherence of the frames):

  `(frame b).hom = ((pullbackComp p a).app _ ≪≫ (pullbackCongr h).app _).inv ≫
     p^*((frame a).hom) ≫ (tildePullbackAlgebraIso R A (E.obj a)).hom ≫ tilde.map (extHom a h)`.

  In words: the frame on `Spec A` is the pullback of the frame on `Spec R`, followed by
  Mathlib/Library's `tildePullbackAlgebraIso` and the system's coefficient-extension
  identification, after the canonical identification `b^* ≅ p^* a^*` of scheme-module pullbacks.
  The proof combines `comparison_comp` (for `toPullback a` and `pullbackComp a p`) with
  `pullback_tildeComparison_comp`.

No hypotheses on `S`, `R` or `A` are imposed.

## Provenance

This is an internal construction for the task that builds root-weight line bundles over arbitrary
base schemes. It supplies the canonical affine comparisons `a^* L ≅ (M_a)^~` and their
coherence under coefficient extension for any sheaf realized from an affine test system. These
are the standard compatibilities between a quasi-coherent sheaf, its pullbacks to affine
schemes, and the associated sheaves of modules.
