# Proof of unique gluing of module morphisms over a scheme open cover

This module proves the published proposition
`Langlands.Scheme.Modules.OpenCoverHomGluingStatement.{u}` from
[`OpenCoverHomGluingStatement`](OpenCoverHomGluingStatement.md), which it
imports unchanged. It also imports
[`ModuleLocalHomPullbackProofs`](../ModuleLocalHomPullbackProofs.md) for the
comparison `restrictCompIso` between restriction along a composite open
immersion and iterated restriction.

## Main result

`Langlands.Scheme.Modules.OpenCoverHomGluing.openCoverHomGluing` is the theorem

```lean
theorem openCoverHomGluing : OpenCoverHomGluingStatement.{u}
```

for an arbitrary universe `u`. It holds for every scheme `X : Scheme.{u}`,
every open cover `𝒰 : X.OpenCover.{u}` with maps `uᵢ := 𝒰.f i`, every pair
`M N : X.Modules` and every family `φᵢ : uᵢ* M ⟶ uᵢ* N` of morphisms between
the actual pullbacks (`Scheme.Modules.pullback`). It assumes the overlap
equation of the statement for every ordered pair `i, j`:

```text
p₁*(φᵢ) ≫ (squarePullbackIso uⱼ p₁ p₂ uᵢ pullback.condition N).hom
  = (squarePullbackIso uⱼ p₁ p₂ uᵢ pullback.condition M).hom ≫ p₂*(φⱼ),
```

where `p₁, p₂` are the projections of `Uᵢ ×[X] Uⱼ`. It concludes
`∃! f : M ⟶ N, ∀ i, uᵢ*(f) = φᵢ`. No other hypothesis is used. The theorem
depends only on the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Strategy

The proof does not use the internal Hom sheaf. It works with sections:

1. **Glue.** A family of linear maps on the sections over all opens contained
   in members of a covering family of opens, compatible with restriction and
   with each other, glues to a morphism of modules. The glued sections come
   from the sheaf condition of `N`; uniqueness comes from its separatedness.
2. **Transport.** Each `φᵢ` is turned into a morphism of restrictions
   `M.restrict uᵢ ⟶ N.restrict uᵢ` through Mathlib's
   `restrictFunctorIsoPullback`, and then into maps on the sections of `M` and
   `N` over opens of `X` inside the range of `uᵢ`.
3. **Overlap.** The statement's overlap equation implies that the maps coming
   from `φᵢ` and `φⱼ` agree on every open inside both ranges.
4. **Assembly.** The glued morphism pulls back to each `φᵢ`, and any morphism
   with these pullbacks agrees with it on every open inside some range.

All declarations below are in namespace
`Langlands.Scheme.Modules.OpenCoverHomGluing`.

## Gluing (section `Glue`)

Fix `X`, an index type `ι` and a family `V : ι → X.Opens`. The hypothesis
`hV : ∀ x : X, ∃ i, x ∈ V i` says that the `V i` cover `X`.

- `sheafAb N` is the underlying `TopCat.Sheaf Ab X` of a module `N`, built
  from `N.presheaf` and `N.isSheaf`.
- `le_iSup_inf hV O`: every open `O` satisfies `O ≤ ⨆ k, O ⊓ V k`.
- `map_map_eq` and `map_le_refl`: functoriality of the restriction maps of a
  module, evaluated on sections.
- `eq_of_local hV s t h`: two sections over `O` whose restrictions to every
  `O ⊓ V k` agree are equal. This is Mathlib's
  `TopCat.Sheaf.eq_of_locally_eq'` for `sheafAb N`.
- `hom_map_app f h x`: a module morphism commutes with restriction on
  sections (naturality of `f.mapPresheaf`).
- The structure `LocalFamily V M N` consists of maps
  `θ i P hP : Γ(M, P) ⟶ Γ(N, P)` for each `i` and each open `P ≤ V i`, with
  the fields `nat` (compatibility with restriction to a smaller open),
  `smul` (linearity over `Γ(X, P)`) and `compat`
  (`θ i P hi = θ j P hj` whenever `P ≤ V i` and `P ≤ V j`).
- `LocalFamily.exists_glue`: for `x : Γ(M, O)`, the sections
  `θ k (O ⊓ V k) (x|_{O ⊓ V k})` agree on pairwise intersections, by `nat`
  and `compat`. Mathlib's `TopCat.Sheaf.existsUnique_gluing'` gives a section
  of `N` over `O` restricting to them.
- `LocalFamily.glue D hV O x` is the section chosen by `exists_glue`.
  `glue_spec₀` records its defining property. `glue_spec` extends it: for any
  `Q ≤ O` with `Q ≤ V i`, the restriction of the glued section to `Q` is
  `θ i Q` applied to the restriction of `x`. It is proved with `eq_of_local`.
- `glue_add`, `glue_smul` and `glue_map`: the glued section is additive in
  `x`, linear over `Γ(X, O)`, and compatible with restriction. Each is proved
  by comparing restrictions to the `O ⊓ V k` with `eq_of_local`.
- `LocalFamily.presheafHom` is the resulting morphism of abelian presheaves,
  and `LocalFamily.hom D hV : M ⟶ N` is the module morphism built from it with
  `PresheafOfModules.homMk` and `glue_smul`.
- `hom_app_apply` (definitional) and `hom_app`: if `P ≤ V i`, then
  `(D.hom hV).app P = D.θ i P hP`.
- `hom_ext_of_local hV f g h`: two morphisms `M ⟶ N` with
  `f.app P = g.app P` for every open `P` inside some `V i` are equal. The proof
  applies `eq_of_local` to each section and moves the restriction through `f`
  and `g` with `hom_map_app`.

## Transport (section `Transport`)

Fix an open immersion `f : U ⟶ X` and modules `M N : X.Modules`.

- `le_image_preimage`: if `P ≤ f.opensRange` then `P ≤ f ''ᵁ f ⁻¹ᵁ P`.
- `transport f ψ P hP`, for `ψ : M.restrict f ⟶ N.restrict f` and
  `P ≤ f.opensRange`, is the composite

  ```text
  Γ(M, P) → Γ(M, f ''ᵁ f ⁻¹ᵁ P) ≅ Γ(M.restrict f, f ⁻¹ᵁ P)
          → Γ(N.restrict f, f ⁻¹ᵁ P) ≅ Γ(N, f ''ᵁ f ⁻¹ᵁ P) → Γ(N, P),
  ```

  of restriction maps of `M` and `N` (the opens `P` and `f ''ᵁ f ⁻¹ᵁ P` are
  equal), Mathlib's `restrictAppIso`, and `ψ.app (f ⁻¹ᵁ P)`.
- `transport_eq`: for any `A : U.Opens` and any morphisms
  `p : op P ⟶ op (f ''ᵁ A)` and `q : op (f ''ᵁ A) ⟶ op P`, `transport` is the
  same composite with `A` in place of `f ⁻¹ᵁ P`. Since `p` and `q` force
  `P = f ''ᵁ A`, injectivity of `f` gives `f ⁻¹ᵁ P = A`, and the two composites
  agree definitionally.
- `restrict_hom_map`, `restrictAppIso_inv_smul`, `restrictAppIso_hom_smul`,
  `restrict_hom_smul` and `scalar_map_map` read naturality and linearity of
  `ψ` through `restrictAppIso`.
- `transport_map` and `transport_smul`: `transport` commutes with restriction
  to a smaller open and is linear over `Γ(X, P)`.

## Overlap compatibility (section `Overlap`)

Here `compHom a b c h N : a* (b* N) ⟶ c* N` is the published comparison from
`Langlands.SchemeModule.RigidifiedModule`, attached to an equation
`a ≫ b = c`.

- `conj_eq a b c h φ`: let `a ≫ b = c` be open immersions and
  `φ : b* M ⟶ b* N`. Conjugating `a*(φ)` by `compHom a b c h` and moving to
  restrictions along `c` with `restrictFunctorIsoPullback c` gives the
  restriction along `a` of the restriction counterpart of `φ`, conjugated by
  `restrictCompIso a b c h`. The proof uses the published
  `restrictCompIso_hom_app_comp` and naturality of
  `restrictFunctorIsoPullback a`.
- `squarePullbackIso_hom_compHom`: for a commutative square `p' ≫ t = s ≫ p`,
  `(squarePullbackIso p p' s t hs M).hom ≫ compHom s p (p' ≫ t) hs.symm M`
  equals `compHom p' t (p' ≫ t) rfl M`. It follows by unfolding
  `squarePullbackIso`, `compHom` and `pullbackCongr`.
- `conj_square`: an equation of the form used in the statement,
  `p'*(φt) ≫ α_N.hom = α_M.hom ≫ s*(φp)` with `α = squarePullbackIso`, implies
  that the conjugates
  `inv (compHom p' t _ _ M) ≫ p'*(φt) ≫ compHom p' t _ _ N` and
  `inv (compHom s p _ _ M) ≫ s*(φp) ≫ compHom s p _ _ N` are equal.
- `restrictHom f φ`, for `φ : f* M ⟶ f* N`, is the morphism
  `M.restrict f ⟶ N.restrict f` obtained by conjugating `φ` with
  `restrictFunctorIsoPullback f`. `transport_restrictHom_eq` is
  `transport_eq` written out for `restrictHom f φ`.
- `transport_compat`: let `ui : Ui ⟶ X`, `uj : Uj ⟶ X`, `p' : Z ⟶ Ui` and
  `s : Z ⟶ Uj` be open immersions with `p' ≫ ui = s ≫ uj` and
  `ui.opensRange ⊓ uj.opensRange ≤ (p' ≫ ui).opensRange`. Assume that the
  conjugates of `p'*(φi)` and `s*(φj)` by the comparisons to `(p' ≫ ui)*` are
  equal. Then
  `transport ui (restrictHom ui φi) P = transport uj (restrictHom uj φj) P`
  for every open `P` inside both ranges. The proof applies `conj_eq` to both
  factorizations of `c := p' ≫ ui` and combines them with the assumption. This
  identifies the iterated restrictions of the two restriction counterparts. It
  writes `P = c ''ᵁ W`, evaluates at `W`, and unfolds `restrictCompIso` into
  its `restrictFunctorCongr` and `restrictFunctorComp` components. On sections
  these are restriction maps. `transport_restrictHom_eq` with `A = p' ''ᵁ W`,
  respectively `A = s ''ᵁ W`, then matches both sides.

## Identifying pullbacks (section `Main`)

For an open immersion `f : U ⟶ X`:

- `restrictHom_pullback_map`: `restrictHom f ((pullback f).map g)` equals
  `(restrictFunctor f).map g`, by naturality of `restrictFunctorIsoPullback`.
- `pullback_map_eq_of_app`: if `g.app (f ''ᵁ W) = (restrictHom f φ).app W` for
  every `W : U.Opens`, then `(pullback f).map g = φ`. The isomorphisms of
  `restrictFunctorIsoPullback` are cancelled.
- `app_image_eq_of_pullback_map`: the converse implication.
- `transport_image`: `transport f ψ (f ''ᵁ W) _ = ψ.app W`.

## Proof of the main theorem

Let `X`, `𝒰`, `M`, `N`, `φ` and the overlap hypothesis `hφ` be given. The
ranges `V i := (𝒰.f i).opensRange` cover `X` by `𝒰.covers`. Define a
`LocalFamily V M N` by `θ i := transport (𝒰.f i) (restrictHom (𝒰.f i) (φ i))`:

- `nat` and `smul` are `transport_map` and `transport_smul`;
- `compat` is `transport_compat` with `p' := pullback.fst`,
  `s := pullback.snd` and the equation `pullback.condition`. The range
  condition is Mathlib's `IsOpenImmersion.range_pullback_to_base_of_left`.
  The equality of conjugates is `conj_square` applied to `hφ i j`.

By `hom_app` and `transport_image`, the glued morphism `D.hom hV` satisfies
`(D.hom hV).app (𝒰.f i ''ᵁ W) = (restrictHom (𝒰.f i) (φ i)).app W` for all
`i` and `W`. Then `pullback_map_eq_of_app` gives `(pullback (𝒰.f i)).map
(D.hom hV) = φ i`, which is existence. For uniqueness, let `g` satisfy
`(pullback (𝒰.f i)).map g = φ i` for all `i`. By `hom_ext_of_local` it
suffices to compare `g.app P` and `(D.hom hV).app P` for `P` inside some range
`V i`. Writing `P = 𝒰.f i ''ᵁ W`, both equal
`(restrictHom (𝒰.f i) (φ i)).app W`, by the display above and by
`app_image_eq_of_pullback_map`.

## Provenance

The statement's paired Markdown cites Stacks Project, Modules, Section 17.22
(tag 01CM) for the principle that module morphisms form a sheaf. This proof
implements that principle conceptually. Local morphisms are glued with the
sheaf condition of the codomain, and uniqueness follows from its
separatedness. The proof does not formalize the cited sheaf
`U ↦ Hom(F|_U, G|_U)` or use the Library's `internalHom`. The section-level
gluing, the transport through `restrictFunctorIsoPullback`, and the reduction
of the `squarePullbackIso` hypothesis to iterated restriction are internal to
this module.
