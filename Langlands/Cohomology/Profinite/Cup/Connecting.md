# Cup products and connecting maps

`Langlands/Cohomology/Profinite/Cup/Connecting.lean`, namespace `Langlands.ProfiniteCohomology`.

For a short exact sequence `0 → A → A' → A'' → 0` that stays exact after tensoring with `B`,
`δ(x ∪ y) = δx ∪ y` (and the corresponding formula with `B` on the left, with sign).

## Declarations

- `cochainOf_cochainsMap_f`, `δ_cohomologyπ_of_lift`, `exists_cocycle_map_f_eq_d`: the connecting map
  on cocycles, through a lift and its differential.
- `isSmoothRep_map_tensorRight_X₁` … `X₃`, `isSmoothRep_map_tensorLeft_X₁` … `X₃`: smoothness of the
  tensored sequences.
- `δ_cup_of_shortExact_tensorRight`, `δ_cup_of_shortExact_tensorLeft`: the compatibility of `δ` with
  cup products.

## Source and licence

Ported from `src/GroundTheory/ProfiniteCohomology/CupProducts/ExistsCocycleMapFEqD.lean` of the repository `leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`. The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). Names are
the source's (the file was named after its first lemma).

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008;
  corrected printing 2013), chapter I, §4, Proposition (1.4.3), p. 38 (`δ(α'' ∪ β) = δα'' ∪ β` and
  `(-1)^p δ(α ∪ β'') = α ∪ δβ''`).
