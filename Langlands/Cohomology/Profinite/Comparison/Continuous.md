# Comparison with Mathlib's continuous cohomology

`Langlands/Cohomology/Profinite/Comparison/Continuous.lean`, namespace
`Langlands.ProfiniteCohomology`.

Mathlib defines `continuousCohomology n X` for a topological representation `X : TopRep k G` by
homogeneous continuous cochains, iterated in `C(G, C(G, …))`. For a discrete `X` whose underlying
representation is smooth, and a locally compact topological group `G` (for instance a profinite
group), this file gives an isomorphism with the cochain model `cohomology`, natural in the group
and the coefficients. Through it every statement of the Library in `continuousCohomology` (class
field theory, the Brauer group comparison) applies to the cochain model, and conversely.

## Declarations

- `underlyingRep X`: the representation underlying a topological representation;
  `underlyingRep_ρ_apply`.
- `discreteTopRep A`: a representation over a discrete ring, with the discrete topology on its
  carrier, as a `TopRep`.
- `finConsHomeomorph`, `nestedHomeomorph X m : resolutionX X m ≃ₜ C(Fin m → G, X)` (uncurrying the
  iterated continuous maps of Mathlib's standard resolution), `nestedLinearEquiv`, and their
  formulas for addition, scalars, the group action (`nestedHomeomorph_ρ_apply`) and the
  differential (`nestedHomeomorph_d_apply`).
- `continuous_partialProd`, `isLocallyConstant_ρ_apply`, `homogeneousFun`,
  `toInhomogeneous`, `ofInhomogeneous`: the passage between homogeneous invariant cochains and
  inhomogeneous locally constant cochains (`φ(g₁,…,gₙ) = σ(1, g₁, g₁g₂, …)` and back).
- `homogeneousEquiv X n`: the linear equivalence of locally constant `n`-cochains with the
  invariants of `resolutionX X (n+1)`; `homogeneousEquiv_symm_d`: it commutes with differentials.
- `cochainsIsoHomogeneousCochains X`: the isomorphism of complexes.
- `isoContinuousCohomology X n : cohomology (underlyingRep X) n ≅ (forget₂ _ _).obj
  (continuousCohomology n X)`, and `linearEquivContinuousCohomology X n`, its linear equivalence.
- `underlyingHom φ f`: the morphism of representations underlying `f : TopRep.res φ X ⟶ Y`.
- `nestedHomeomorph_resolutionMap`, `comp_partialProd`, `toInhomogeneous_cochainsMap`,
  `cochainsMap_comp_cochainsIsoHomogeneousCochains_hom`: Mathlib's `ContinuousCohomology.cochainsMap`
  corresponds to `cochainsMap` under the isomorphism of complexes.
- `isoContinuousCohomology_naturality`: for `φ : H →ₜ* G` and `f : TopRep.res φ X ⟶ Y`,
  `map φ (underlyingHom φ f) n ≫ (isoContinuousCohomology Y n).hom =
  (isoContinuousCohomology X n).hom ≫ (forget₂ _ _).map (ContinuousCohomology.map φ f n)`.
- `Langlands.Continuous.DiscreteModule.ofSmoothRep A`: a smooth representation over a discrete
  ring, with the discrete topology, as a discrete module of `Langlands.Continuous` (the action is
  jointly continuous since orbit maps are locally constant); `ofSmoothRep_toRep`.
- `isoContinuousCohomologyDiscrete A n`, `linearEquivContinuousCohomologyDiscrete A n`: the case
  `X = discreteTopRep A`.

## Source and licence

Ported from `src/GroundTheory/ProfiniteCohomology/BridgeDefs.lean`, `BridgeNested.lean` and
`Bridge.lean` of the repository `leanprover-community/riemann-hypothesis`
(<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`. The repository
has no licence file; its text is used with attribution
(`licenses/RiemannHypothesis/SOURCE.md`). Source names: `cohomologyIsoContinuousCohomology` →
`isoContinuousCohomology`, `cohomologyLinearEquivContinuousCohomology` →
`linearEquivContinuousCohomology`, `cohomologyIsoContinuousCohomologyDiscrete` →
`isoContinuousCohomologyDiscrete`, `cohomologyLinearEquivContinuousCohomologyDiscrete` →
`linearEquivContinuousCohomologyDiscrete`; the others are unchanged. New (not in the source):
`underlyingHom`, `nestedHomeomorph_resolutionMap`, `comp_partialProd`,
`toInhomogeneous_cochainsMap`, `cochainsMap_comp_cochainsIsoHomogeneousCochains_hom`,
`isoContinuousCohomology_naturality` (the source has the isomorphism objectwise only) and
`DiscreteModule.ofSmoothRep` (built from the source's `discreteTopRep`). The naturality theorem
is proved with `backward.isDefEq.respectTransparency false`: the homology of the image of a
complex under `forget₂` and the homology of the image of its short complex are definitionally,
not reducibly, equal.

## References

- J.-P. Serre, *Galois Cohomology* (English translation of *Cohomologie galoisienne*, Springer 1997;
  corrected printing 2002), chapter I, §2.2, p. 10 (continuous cochains).
- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008;
  corrected printing 2013), chapter I, §2, pp. 13–14 (homogeneous cochains and Definition (1.2.2),
  p. 13; the isomorphism with inhomogeneous cochains, `y(σ₁, …, σₙ) = x(1, σ₁, σ₁σ₂, …, σ₁⋯σₙ)`,
  p. 14).
