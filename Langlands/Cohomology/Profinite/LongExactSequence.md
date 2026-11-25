# The long exact cohomology sequence

`Langlands/Cohomology/Profinite/LongExactSequence.lean`, namespace `Langlands.ProfiniteCohomology`.

A short exact sequence `S : 0 → A → B → C → 0` of smooth representations gives a short exact
sequence of complexes of locally constant cochains: a locally constant cochain with values in
`C` lifts to one with values in `B` by composing with a set-theoretic section of `B → C`.
Hence the long exact sequence
`⋯ → Hⁱ(G, A) → Hⁱ(G, B) → Hⁱ(G, C) → Hⁱ⁺¹(G, A) → ⋯`.

## Declarations

- `cochainsShortComplex S`, `cochainsShortComplex_shortExact`: the short complex of cochain
  complexes and its exactness.
- `δ hS i j hij : Hⁱ(G, C) ⟶ Hʲ(G, A)` for `hS : S.ShortExact` and `hij : i + 1 = j`, the
  connecting map; `δ_comp`, `comp_δ`, `map_f_comp_g`: consecutive maps compose to zero.
- `cohomology_exact₁` (at `Hʲ(G, A)`), `cohomology_exact₂` (at `Hⁱ(G, B)`), `cohomology_exact₃`
  (at `Hⁱ(G, C)`): exactness.
- `cochainsShortComplexMap`, `δ_naturality`: the connecting map is natural for morphisms of short
  exact sequences.
- `cochainsShortComplexMapAlong`, `δ_comp_map`: the connecting map commutes with maps along a
  continuous homomorphism `φ : H →ₜ* G`, for a morphism `S.map (Rep.resFunctor φ) ⟶ T` to a short
  exact sequence `T` of `H`-representations.
- `shortExact_map_res`, `δ_comp_res`: restriction of a short exact sequence to a subgroup is
  short exact and commutes with `δ`; instances for the smoothness of the restricted terms.
- `quotientToInvariantsFunctor_preservesZeroMorphisms`, `mapQuotientToInvariantsResToSelf`,
  `δ_comp_infl`: inflation commutes with `δ`, when the sequence of `N`-invariants is short exact.

## Source and licence

Ported from `src/GroundTheory/ProfiniteCohomology/ContinuousCochains/LongExactSequence.lean` and
`src/GroundTheory/ProfiniteCohomology/CohomologyFunctoriality/QuotientToInvariantsFunctorPreservesZeroMorphism.lean`
of the repository `leanprover-community/riemann-hypothesis`
(<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`. The repository
has no licence file; its text is used with attribution
(`licenses/RiemannHypothesis/SOURCE.md`). Source names: `cohomologyMap_f_comp_g` →
`map_f_comp_g`, `δ_comp_cohomologyMapAlong` → `δ_comp_map`, `δ_comp_cohomologyRes` →
`δ_comp_res`, `δ_comp_cohomologyInfl` → `δ_comp_infl`, `isDiscreteRep_map_*` →
`isSmoothRep_map_*`; the others are unchanged. The maps are the single `map` of
`Functoriality.lean`; the coefficient zero lemmas (`cochainsMap_zero`, `cohomologyMap_zero`) moved
there.

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008;
  corrected printing 2013), chapter I, §3, Theorem (1.3.2), p. 27.
- J.-P. Serre, *Galois Cohomology* (English translation of *Cohomologie galoisienne*, Springer 1997;
  corrected printing 2002), chapter I, §2.2, p. 11 (the `H^q(G, ·)` are the derived functors of
  `A ↦ A^G` on discrete modules).
