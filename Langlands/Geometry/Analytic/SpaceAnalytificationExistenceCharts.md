# Covering families of étale affine charts

Unconditional algebraic geometry (derived provenance) used by the conditional existence
argument. It is the chart choice of Conrad–Temkin (2009), §4.3: cover an étale atlas by
affine opens.

- `atlasChart W`, `atlasChartι W`, `chartAlgebra W`, `chartIso W`, `chartMap W`: for an
  affine open `W` of an atlas `U` over `Spec K`, these are
  - the open subscheme over `Spec K` and its inclusion into `U`;
  - its coordinate algebra `Aᵂ = Γ(W)`;
  - the comparison `W ≅ Spec Aᵂ` (`affineSchemeOverIso`);
  - the composite `Spec Aᵂ → U`.

  `etale_chartMap_left` records that this composite is étale (isomorphism followed by an
  open immersion).
- `nonempty_chartData`: an algebraic space `X` that is locally of finite type over `Spec K`
  has `ChartData X`. Construction:
  - Take an étale surjective atlas `a : U → X` with `U` locally of finite type
    (`LocallyOfFiniteTypeOverBase.exists_atlas`).
  - The charts are the affine opens `W` of `U`, with points `Spec Aᵂ → U → X`. These are
    étale by `isEtale_map` and `IsEtale.comp`, and `Aᵂ` is of finite type.

  Covering property, for `y : Spec B → X` and a prime `𝔭`:
  1. Form the represented pullback `V = U ×_X Spec B`. Its projection to `Spec B` is
     surjective (`IsSurjective.projection`), so pick `v ∈ V` over `𝔭`.
  2. Choose an affine open `W ∋ φ(v)` of `U`.
  3. For any model `M` of `Spec B ×_X Spec Aᵂ`, the open subscheme `φ⁻¹(W) ⊆ V` maps to
     `Spec B` and to `W ≅ Spec Aᵂ` compatibly over `X` (`morphismRestrict_ι`), hence to
     `Spec M.C`.
  4. The image of `v` is a prime of `M.C` lying over `𝔭` (`Spec.map_apply`).
