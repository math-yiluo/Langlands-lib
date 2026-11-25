# Identity jets inside an affine open containing the unit section

This internal module describes the identity jets of a separated group by
commutative algebra. It is the first step toward
`IdentityJetLocallyFreeStatement`.

## Arbitrary base

Let `G` be a group scheme over a scheme `S` with separated structure
morphism. Let `V` be an affine open of `G.X.left` containing the image of
the unit section (`G.identitySection ⁻¹ᵁ V = ⊤`).

- `IdentityJet.inclusion_preimage_eq_top`: the jet lies inside `V`. The image
  of the jet inclusion is the image of the unit section (Library
  `range_inclusion_eq_range_identitySection`).
- `IdentityJet.affineChartIso`: the order-`n` jet is isomorphic to
  `Spec (Γ(G, V) ⧸ I(V))`, where `I` is the jet ideal sheaf. The
  isomorphism is the member of Mathlib's affine cover of the closed
  subscheme indexed by `V`. It is an open immersion whose range is the
  preimage of `V`, which is everything
  (`isIso_of_isOpenImmersion_of_opensRange_eq_top`).
  `IdentityJet.affineChartIso_inv_inclusion` identifies its inverse followed
  by the jet inclusion with `Spec` of the quotient map followed by
  `V.fromSpec`.
- `IdentityJet.ideal_ideal_eq`: on `V`, the jet ideal is the `(n + 1)`-st
  power of the kernel of evaluation at the unit section
  (`Scheme.Hom.ker_apply`, using that the unit section is a closed immersion).

## Affine base

Now let the base be `Spec R`.

- `IdentityJet.chartRingHom` makes `Γ(G, V)` an `R`-algebra, through the
  structure morphism and `Γ(Spec R, ⊤) ≅ R`.
  `IdentityJet.chartAugmentation` is evaluation at the unit section, a ring
  map to `R`. `chartAugmentation_chartRingHom` shows it is a retraction,
  because the unit section is a section of the structure morphism.
- `IdentityJet.ker_chartAugmentation` and
  `IdentityJet.ideal_eq_ker_chartAugmentation_pow`: the jet ideal on `V` is
  the `(n + 1)`-st power of the augmentation ideal.
- `IdentityJet.smooth_chartRingHom`: if `G` is smooth, `Γ(G, V)` is a smooth
  `R`-algebra (Mathlib's `Smooth.smooth_appLE` composed with an isomorphism).
- `IdentityJet.chartJetAlgebra` is the `R`-algebra `Γ(G, V) ⧸ I(V)`.
  `IdentityJet.chartJetAlgebra_finite_projective` shows that it is finite and
  projective over `R` when `G` is smooth. The augmentation-ideal quotient of
  a formally smooth algebra of finite type is finite projective (the
  Library's `Algebra.FormallySmooth.finite_projective_quotient_ker_pow`,
  used in `Langlands.RingTheory.Smooth.SectionJetFiltration`). The two ideals
  agree by the previous item.
- `IdentityJet.chartJetIso` and `IdentityJet.chartJetIso_projection`: the jet
  is `Spec` of `chartJetAlgebra`, and the isomorphism turns the jet
  projection into `Spec` of the structure map `R → chartJetAlgebra`. The
  proof uses Mathlib's `SpecMap_appLE_fromSpec` and
  `Scheme.isoSpec_Spec_inv`.

This is the algebraic description, for smooth groups, of the normal
invariants of SGA 3, Exposé XVI, Proposition 3.1. It adds no geometric input
beyond the Library's identity jets and Mathlib's closed-subscheme API.
