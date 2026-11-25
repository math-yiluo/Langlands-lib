# The duality pairing: functoriality, sums and connecting maps

`Langlands/Cohomology/Profinite/Duality/Pairing.lean`, namespace
`Langlands.ProfiniteCohomology`.

Properties of the duality map `Hʳ(G, M) → Hom(Hˢ(G, M*), ℤ/n)` of `DualModule.lean` used in the
dévissage: it is natural in `M`, it is bijective for a finite direct sum when it is for the
summands, every finite smooth module killed by `n` embeds into a finite sum of coinduced modules
`Coind_W^G ℤ/n`, and cup products with connecting maps anticommute.

## Declarations

Naturality and sums.

- `cohomologyMap_finsetSum`, `dualMap_add`, `dualMap_zero`, `dualMap_finsetSum`: additivity of
  coefficient maps and of `dualMap`.
- `cupPairing_evalPairing_cohomologyMap`, `dualityMap_cohomologyMap`: for `f : A → B`,
  `⟨f_* x, y⟩ = ⟨x, (f*)_* y⟩` for the evaluation pairings and the duality maps.
- `bijective_dualityMap_of_sum`: if `P` is a retract-sum of modules `X_j`
  (`∑ p_j ≫ i_j = 𝟙`) and the duality maps of the `X_j` are bijective, so is that of `P`.
- Instances `hasFiniteBiproducts_rep`, `finite_biproduct`, `isSmoothRep_dualRep_biproduct`;
  `biproduct_eq_sum`; `bijective_dualityMap_biproduct` (finite biproducts, total degree `2`).

Embedding into coinduced modules.

- `fixingOpenSubgroup M`: for a finite smooth `M`, an open subgroup acting trivially
  (`fixingOpenSubgroup_apply`).
- `charHom W M hW χ`: a character `M → ℤ/n` as a morphism of `W`-modules when `W` acts
  trivially (`charHom_hom_apply`).
- `exists_injective_biproduct_coind`: a finite smooth module killed by `n` embeds into a finite
  biproduct of copies of `Coind_W^G ℤ/n` for some open subgroup `W`.

Cup products and connecting maps.

- `cupCochain_pairing_left`, `cupCochain_pairing_right`: compatibility of cochain cup products
  with pairings of short complexes `S`, `T` compatible with `μ₁, μ₂, μ₃`.
- `cupPairing_δ_add_cupPairing_δ`, `cupPairing_δ_eq`: for short exact `S`, `T` and compatible
  pairings, `δx ∪ y = (-1)^{p+1} x ∪ δy`.

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis`
(<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, files
`src/GroundTheory/ProfiniteCohomology/PoincareDuality/CupPairingEvalPairingCohomologyMap.lean`
and `src/GroundTheory/ProfiniteCohomology/PoincareDuality/DeltaPairing.lean`. The repository has
no licence file; its text is used with attribution
(`licenses/RiemannHypothesis/SOURCE.md`). Names are the source's (the coefficient maps
`cohomologyMap f n` of the source are `coeffMap f n`; lemma names keep `cohomologyMap`).

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, chapter I, §4,
  proposition 1.4.3 (cup products and connecting maps), and chapter III, §4; page references to
  be added.
