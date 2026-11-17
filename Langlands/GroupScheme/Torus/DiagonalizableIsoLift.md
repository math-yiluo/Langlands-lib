# Lifting isomorphisms of diagonalizable groups to their free covers

All schemes lie in an arbitrary universe `u`. For finitely generated abelian
groups `Λ, Λ'` with free covers `F(Λ), F(Λ')` (module `FreeCharacterCover`),
this module lifts every isomorphism of group schemes
`u : D_X(Λ) ≅ D_X(Λ')` over an arbitrary scheme `X` to an isomorphism
`liftIso u : D_X(F(Λ)) ≅ D_X(F(Λ'))`. The lift is compatible with the
projections, with pullback, with composition and with identities. An
isomorphism `u` is only locally of the form `D(g)`, so the lift is built on
the disjoint open loci where `u = D(g)` for a fixed `g`.

## Local tools

- `toSpecZ_comp`: every map to `Spec ℤ` is the canonical one.
- `baseChange_hom_ext_of_opens`: two homomorphisms between base changes
  `f*G ⟶ f*H` (for `f : X ⟶ S`) are equal if every point of `X` has an open
  neighbourhood on which their restrictions (`pullHom`) agree. The proof
  compares the first pullback projections pointwise, using
  `Scheme.hom_ext_of_forall` and the preimages of the given opens.
- `dpull q φ` is the restriction of `φ : D_X(Λ) ⟶ D_X(Λ')` along `q : Y ⟶ X`,
  as a map `D_Y(Λ) ⟶ D_Y(Λ')`. It is the published `pullHom` along the
  identifications of the diagonalizable groups as base changes from
  `Spec ℤ`. `dpull_eq` writes it with `diagonalizableBaseChangeIso`.
  Laws: `dpull_id`, `dpull_comp`, `dpull_dpull`, `dpull_identity`,
  `dpull_dpull_of_comm`, and `dpull_diagonalizableMap`
  (`dpull q (D_X(g)) = D_Y(g)`). `dpullIso` is the version for isomorphisms.
- `dhom_ext` and `diso_ext`: maps of diagonalizable groups that agree on an
  open cover are equal (from `baseChange_hom_ext_of_opens`).
- `exists_open_dpull` (local rigidity): every `u : D_X(Λ) ⟶ D_X(Λ')` restricts
  to some `D_V(g)` on an open neighbourhood `V` of any point. This is Worker
  736's `exists_opens_baseChange_map_eq` (module
  `RelativeDiagonalizableHomLocality`). `dpull_of_le` shrinks `V`.
  `eq_of_dpull` says that `g` is unique on a nonempty open, by the injectivity
  result of the same module.
- `diagonalizableIso X g` is the isomorphism `D_X(g)` for `g : Λ' ≃+ Λ`.

## The loci

- `locus u g` is the union of all opens on which `u` restricts to `D(g)`.
  `le_locus` and `mem_locus` describe it.
- `locus_disjoint`: for `g ≠ g'` the loci are disjoint, by `eq_of_dpull`.
- `locus_cover`: for an isomorphism `u`, every point lies in some
  `locus u.hom g` with `g` an isomorphism. Local rigidity for `u.hom` and
  `u.inv` gives `g, g'` near the point. Then `eq_of_dpull` applied to
  `u.hom ≫ u.inv = 𝟙` and `u.inv ≫ u.hom = 𝟙` shows that `g` and `g'` are
  inverse. `exists_open_dpull_iso` restates this.
- `locus_isIso`: the loci form a disjoint open cover, so
  `∐_g locus u.hom g ⟶ X` is an isomorphism (Mathlib's
  `nonempty_isColimit_cofanMk_of`).

## The lift

- `liftIso u` is assembled with the published
  `DisjointComponents.pullbackIsoAlong` (module `DisjointPullbackCoherence`)
  from the isomorphisms `D(F(g)) = diagonalizableIso (coverEquiv g)` on the
  loci.
- `dpull_liftIso`: on any open where `u = D(g)`, the lift is `D(F(g))`.
- `liftIso_comm`: `u.hom ≫ D(proj Λ') = D(proj Λ) ≫ (liftIso u).hom`. This is
  checked locally, using `proj ∘ F(g) = g ∘ proj`.
- `dpull_liftIso_hom` and `liftIso_dpullIso`: the lift commutes with
  pullback. `liftIso_trans`, `liftIso_refl` and `liftIso_diagonalizableIso`
  (`liftIso (D(g)) = D(F(g))`) all follow from `diso_ext` and
  `dpull_liftIso`, together with the functoriality of `coverEquiv`.

Provenance: internal. The construction follows the idea in Conrad,
*Reductive group schemes* (2014), proof of Proposition B.3.8, of making
choices of character groups compatible on overlaps by local constancy. The
specific lifting through the loci of `u` is part of this formalization.
