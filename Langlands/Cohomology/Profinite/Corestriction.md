# Corestriction from an open subgroup

`Langlands/Cohomology/Profinite/Corestriction.lean`, namespace `Langlands.ProfiniteCohomology`.

For a compact group `G`, an open subgroup `U` and a smooth representation `A` of `G`,
corestriction `cores U A n : Hⁿ(U, A) ⟶ Hⁿ(G, A)` is the inverse of Shapiro's isomorphism followed
by the map induced by the trace `Coind_U^G(A) → A`, `f ↦ Σ_{c ∈ G/U} c · f(c⁻¹)`. Restriction
followed by corestriction is multiplication by the index.

## Declarations

- `coindTraceTerm`, `coindTraceTerm_apply`: one term of the trace;
  `coindTrace U A : Rep.coind U.subtype (Rep.res U.subtype A) ⟶ A`, with `coindTrace_hom_apply`;
  `coindUnit_comp_coindTrace`: `coindUnit ≫ coindTrace = [G : U] • 𝟙`.
- `res_eq_coindUnit_shapiroMap`: restriction is `coindUnit` followed by Shapiro's map.
- `map_id_nsmul`: cohomology of `m • f` is `m •` that of `f`.
- `cores U A n`, and `res_comp_cores`: `res A U n ≫ cores U A n = (U : Subgroup G).index • 𝟙 _`.

## Source and licence

Ported from the section `Trace` of `src/GroundTheory/ProfiniteCohomology/ShapiroDefs.lean` and the
section `Corestriction` of `src/GroundTheory/ProfiniteCohomology/Shapiro.lean` of the repository `leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`. The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). Names:
`cohomologyCores` → `cores`, `cohomologyRes_comp_cohomologyCores` → `res_comp_cores`,
`cohomologyRes_eq_coindUnit_shapiroMap` → `res_eq_coindUnit_shapiroMap`; the source's private
`cohomologyMap_nsmul` is the public `map_id_nsmul`. `res_eq_coindUnit_shapiroMap` is proved with
`backward.isDefEq.respectTransparency false`.

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008;
  corrected printing 2013), chapter I, §5, pp. 47–48 (corestriction), and Corollary (1.5.7), p. 51
  (`cor ∘ res = (G : U)`); §6, Proposition (1.6.5), p. 63, identifies corestriction, through
  Shapiro's lemma, with the map induced by `ν(x) = Σ_{σ ∈ G/U} σ x(σ⁻¹)`.
- J.-P. Serre, *Local Fields* (Springer GTM 67, 1979; translation of *Corps locaux*), chapter VII,
  §7, Proposition 6, pp. 118–119 (`Cor ∘ Res = n` for a subgroup of index `n`). Serre works there
  with the cohomology of abstract groups.
