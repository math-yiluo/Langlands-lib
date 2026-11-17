# Invariant sections of equivariant line bundles on cartesian étale relations

Module `Langlands.AlgebraicGeometry.Picard.EquivariantSectionDescent`. Worker 5217, Task 7409.
Internal, derived construction used by the proof `polarizedEtaleRelationEffectivity`.

## Main result

`EquivariantModule.exists_invariant_section` works in one universe `u`. Let `S` and `U` be
affine, and let `p : U ⟶ S` be flat and surjective. Let `E` be an actual étale equivalence
relation and `f : E.U ⟶ U` a morphism with
`hcart : IsPullback E.t (E.s ≫ f) (f ≫ p) p`. Assume the chart `E.U` is compact and
quasi-separated. Let `F` be a module sheaf on `E.U` that is locally free of rank one, with an
`EquivariantModule E F` structure `D`. Then every point `x` of the whole generation open
`trivializationOpen F σ` of a global section `σ` lies in the generation open of some global
section `c` satisfying

```text
E.s ⁻¹ᵁ trivializationOpen F c = E.t ⁻¹ᵁ trivializationOpen F c.
```

No noetherian, finiteness, smoothness or properness hypothesis is used.

## Equivariant modules

`EquivariantModule E F` is the module-level form of the published `EquivariantLineBundle`.
For every scheme `T` and related pair `a b : T ⟶ E.U` it supplies
`transport a b h : (pullback a).obj F ≅ (pullback b).obj F`. These satisfy `transport_self`,
`transport_trans` and `transport_precompose`, the three laws of `EquivariantLineBundle`
with the actual composition comparisons `Scheme.Modules.pullbackComp`.
`EquivariantLineBundle.tensorPowModule B n` packages the tensor-power identifications of
`EquivariantLineBundleTensorPow`, so `F = tensorPow B.bundle.obj n` is an equivariant
module.

## Section calculus (namespace `Langlands.Scheme.Modules`)

- `gpull f M : Γ(M, ⊤) →+ Γ((pullback f).obj M, ⊤)` is the published `sectionPullback f M ⊤`
  on global sections. `gpull_naturality`, `gpull_comp`, `gpull_comp_inv`, `gpull_id` and
  `gpull_congr` restate the published naturality, composition and identity laws, and the
  identification along `pullbackCongr` of equal morphisms.
- `relPull fX fY h w M` is the published `relativeGlobalSectionsPullback` for the `Over`
  morphism `Over.homMk h w`; `relPull_apply` evaluates it as `gpull h M`.
- `residueSection_smul` (the residue-field value is semilinear) and `residueSection_zero`.

`EquivariantModule.tr a b h m := (transport a b h).hom.app ⊤ (gpull a F m)` is the transported
pullback of a global section. Its laws are `tr_self`, `transport_tr` (transitivity),
`pullback_tr` (pullback along `k` corresponds to the pair `(k ≫ a, k ≫ b)`), the congruences
`tr_congr_left/right`, and `transport_precompose_apply`.

## The descent coalgebra

Write `A = Γ(S, ⊤)`, `B = Γ(U, ⊤)` and `φ = p.appTop : A ⟶ B`. Then `U` lies over `Spec B` by
`U.isoSpec.hom`, and
`M = (relativeGlobalSections (f ≫ U.isoSpec.hom)).obj F` is `Γ(E.U, F)` as a `B`-module.

- `isPullback_symm`: the relation's symmetry gives `IsPullback E.s (E.t ≫ f) (f ≫ p) p`.
  The swap `σ` from `E.symm` is an involution by `E.mono_lift`.
- `isPullback_spec`: the same square over `Spec B ⟶ Spec A`, through `isoSpec`.
- `baseChange hcart F : B ⊗_A M ⟶ Γ(E.R, s^*F)` (with `B` acting through `E.t ≫ f`) is the
  published scalar sections base-change map for that square, composed with the identity
  ring-change comparison. `isIso_baseChange` applies the published
  `isIso_scalarSectionsBaseChangeMap_lineBundle_qcqs`. Its inputs are flatness of `φ`,
  affineness of `E.s`, compactness and quasi-separatedness of `E.U`, and the rank-one
  property. `baseChange_homEquiv` says that the adjoint of `baseChange` sends `m` to
  `gpull E.s F m`.
- `transportPull f F D : M ⟶ Γ(E.R, s^*F)` sends `m` to `D.tr E.t E.s m`.
- `coalgebra hcart F hF D` is the coalgebra over the published `descentComonad φ` with
  underlying module `M` and coaction `transportPull ≫ baseChangeIso.inv`.
  - Counit (`counit_eq`, `diagPull_tr`): the comonad counit equals `baseChange ≫ diagPull`.
    Here `diagPull` is pullback along a diagonal relation point `diag E` (from `E.refl`),
    identified with `M`. The transport law at the diagonal shows that the composite is the
    identity.
  - Coassociativity. Let `R₂` be the fibre product of
    `(E.t ≫ f ≫ U.isoSpec.hom) ≫ Spec.map φ` and `Spec.map φ`, with projections `g₂` and
    `f₂`. Then `baseChange₂ : B ⊗_A (B ⊗_A M) ⟶ Γ(R₂, g₂^*s^*F)` is a published base-change
    isomorphism (`isIso_baseChange₂`). The scheme `E.R` is compact and quasi-separated
    because `E.s` is affine. Two relation points `kappa`, `lam : R₂ ⟶ E.R` are defined from
    the transposed square. `kappa` has source `g₂ ≫ E.s`, `lam` has source `g₂ ≫ E.t`, and
    both have target over `f₂`. `kappa_t_eq_lam_t` proves `kappa ≫ E.t = lam ≫ E.t` from
    `E.trans` and uniqueness. With `kPull` (pullback along `kappa`) and `lPull` (pullback
    along `lam` followed by the transport over `g₂`), `delta_eq` gives
    `δ ≫ baseChange₂ = baseChange ≫ kPull` and `map_eq` gives
    `G(coaction) ≫ baseChange₂ = baseChange ≫ lPull`. `kPull_tr_eq_lPull_tr` is the
    transport identity on transported sections. Coassociativity then follows by cancelling
    the isomorphism `baseChange₂`.

## Invariant sections

- `tr_eq_of_mem_coinvariants`: if `c` is coinvariant (`coaction c = 1 ⊗ c`), then
  `D.tr E.t E.s c = gpull E.s F c`.
- `invariant_of_mem_coinvariants`: hence
  `E.s ⁻¹ᵁ trivializationOpen F c = E.t ⁻¹ᵁ trivializationOpen F c`. This uses the published
  `lineBundlePullbackSectionOpen` (generation opens of pulled-back sections are inverse
  images) and `trivializationOpen_mapIso` for the transport isomorphism.
- `faithfullyFlat_appTop`: `φ` is faithfully flat, since `p` is flat and surjective between
  affine schemes.
- `vanishingAt F x`: the `B`-submodule of sections with zero residue-field value at `x`.
  It is closed under addition (published `FiniteSectionAvoidance.residueSection_add`) and under
  scalars (`residueSection_smul`).
- Proof of `exists_invariant_section`. By the published `lineBundleResidueOpenComparison`,
  `x ∈ trivializationOpen F c` iff the residue value of `c` at `x` is nonzero. Suppose no
  section with an invariant generation open contains `x`. Then every coinvariant lies in
  `vanishingAt F x`. The published `descentMap` of the coalgebra, composed with the quotient
  by this submodule, has zero adjoint, so it is zero. The published `bijective_descentMap`
  (faithfully flat descent for coalgebras, through Mathlib's `comonadicExtendScalars`) makes
  the descent map surjective, so `σ` vanishes at `x`, a contradiction.

## Provenance

Derived internal construction. The algebraic input is faithfully flat descent of modules
in coalgebra form, as formalized in the published `FaithfullyFlatCoalgebraDescent`, whose
Markdown cites Stacks Proposition 35.3.9 (Tag 023N). The geometric inputs are published
Library results: qcqs line-bundle flat base change, section pullback, generation opens and
residue values. In the source (Stacks Lemma 99.14.3 in Section 99.14, Tag 0D1L), the
descended object is an algebraic space and Lemma 74.13.1 (Tag 0D3C) works on it with the graded algebra of sections and its
compatibility with flat base change. Here no algebraic space, descended module sheaf or
relative Proj is constructed. Instead, the sections `Γ(X, L^{⊗n})` on the chart carry an
explicit descent coalgebra built from the equivariant transport. Its counit and
coassociativity are verified in Lean.
