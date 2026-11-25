# Cup products of abstract groups and inflation

`Langlands/Cohomology/Profinite/Cup/Inflation.lean`, namespaces `Langlands.ProfiniteCohomology` and
`Langlands.ProfiniteCohomology.GroupCoh`.

The cup product on the cohomology of an abstract group (in particular a finite quotient `G/U`) is
the Library's `Langlands.Tate.ordinaryCup`. Inflation from a finite quotient is multiplicative:
the profinite cup product of inflated classes is the inflation of the cup product of `G/U`.

## Declarations

- `GroupCoh.cupH h`: `Langlands.Tate.ordinaryCup (Langlands.Tate.tensorPairing A B) p q`, transported to
  degree `n` along `h : p + q = n`; `GroupCoh.cupH_π`: on classes of cocycles it is
  `GroupCoh.cupCocycles`, the cup product of cocycles by `cupCochain`.
- `GroupCoh.cocycles_ext`, `GroupCoh.d_iCocycles`, `GroupCoh.d_cupCochain_iCocycles`,
  `GroupCoh.cupCocycle`, `GroupCoh.iCocycles_cupCocycle`, `GroupCoh.cupCocycles`,
  `GroupCoh.iCocycles_cupCocycles`, `GroupCoh.map_π_apply`, `GroupCoh.iCocycles_cocyclesMap`,
  `GroupCoh.map_cupH`: cocycle-level description and naturality in the coefficients.
- `toGroupCohomology_cohomologyπ`, `iCocycles_cyclesMap_cochainsι`, `inflation_π`,
  `cochainOf_cocycleι_cyclesMap_inflationCochains`, `inflationCochains_comp_cochainsMap`,
  `inflation_comp_cohomologyMap`, `cohomologyMap_inflation`: inflation from finite quotients on
  cocycles and its naturality.
- `cup_inflation`: `infl x ∪ infl y = infl (x ∪ y)` (through `invariantsTensorHom`).

## Source and licence

Ported from `src/GroundTheory/ProfiniteCohomology/CupProducts/GroupCohomology.lean` of the repository `leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`. The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). The
declarations of `GroupCoh` are the source's `GroundTheory.GroupCoh` lemmas of
`src/GroundTheory/TateCohomology/CupProduct.lean` that the profinite files use; the source's own cup
product `cupH` (defined by descending cocycles) is replaced by the Library's `ordinaryCup`, and
`cupH_π` is proved from the Library's `ordinaryCup_π_π`.

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008;
  corrected printing 2013), chapter I, §4, pp. 36–38 (cup products), and §5, Proposition
  (1.5.3)(ii), p. 49 (`inf(α ∪ β) = inf α ∪ inf β`).
