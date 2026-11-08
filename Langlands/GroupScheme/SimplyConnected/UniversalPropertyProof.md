# Universal property of a semisimple simply connected central cover

Authors: Worker 1290 and Worker 1362.

The theorem
`Langlands.GroupScheme.simplyConnectedCentralCoverUniversalProperty` proves
exactly the published
`Langlands.GroupScheme.SimplyConnectedCentralCoverUniversalProperty.{u}` from
`Langlands.GroupScheme.SimplyConnected.UniversalPropertyStatement`.

For every field `k : Type u`, actual group schemes `C` and `G` over
`Spec k`, and an actual homomorphism `π : C ⟶ G`, it sends
`IsSimplyConnected C`, `IsSemisimple G` and `IsCentralIsogeny π` to
`HasCentralCoverUniversalProperty π`. Unfolded, for every semisimple `H` and
every central isogeny `q : H ⟶ G` there is a unique actual homomorphism
`a : C ⟶ H` with `a ≫ q = π`. The theorem adds no hypotheses. The field may
be imperfect and of any characteristic, and the universe `u` is arbitrary.
Kernels and centres keep their full scheme-theoretic meaning on all test
schemes, including nonreduced ones, because the proof only uses published
results about the Library's predicates.

## Dependencies

- `Langlands.GroupScheme.centralIsogenyCommonSemisimpleRefinement`, from
  `Langlands.GroupScheme.CentralIsogeny.CommonSemisimpleRefinement`. It proves
  `CentralIsogenyCommonSemisimpleRefinement.{u}`: two central isogenies
  `π : C ⟶ G` and `q : H ⟶ G` between semisimple groups over a field have a
  semisimple `D` with central isogenies `p : D ⟶ C` and `r : D ⟶ H` such that
  `p ≫ π = r ≫ q`. It does not use simple connectedness, cover existence or
  this universal property.
- `IsCentralIsogeny.cancel_of_connectedReductive`, from
  `Langlands.GroupScheme.CentralIsogeny.Uniqueness`. For a connected reductive
  source `C`, a central isogeny `q` and homomorphisms `a b : C ⟶ H` with
  `a ≫ q = b ≫ q`, it concludes `a = b`.
- The two fields of the Library structure `IsSimplyConnected C`:
  `isSemisimple`, and `central_isogeny_isIso`, which says that every central
  isogeny from a semisimple group into `C` is an isomorphism. It also uses the
  field `isConnectedReductive` of `IsSemisimple C`.

The proof does not use `IsSimplyConnectedCover`, its `lift`, `lift_unique`,
`hom_ext` or `iso`. Those helpers take the universal property as a premise.

## Implemented proof

The helper theorem `centralCoverFactorization_of_refinement` takes
homomorphisms `π : C ⟶ G`, `q : H ⟶ G`, `p : D ⟶ C` and `r : D ⟶ H` with
`p ≫ π = r ≫ q`. It also assumes that `C` is simply connected, that `D` is
semisimple and that `p` is a central isogeny. Then
`hC.central_isogeny_isIso D p hD hp` makes `p` an isomorphism. The
homomorphism `inv p ≫ r : C ⟶ H` satisfies
`(inv p ≫ r) ≫ q = inv p ≫ (r ≫ q) = inv p ≫ (p ≫ π) = π`.
These steps are associativity, the commuting square, and `simp`, which
cancels `inv p ≫ p`.

The main theorem introduces `k`, `C`, `G`, `π`, the three hypotheses `hC`,
`hG` and `hπ`, and then the test data `H`, `q`, `hH` and `hq` of
`HasCentralCoverUniversalProperty π`.

1. *Existence.* Apply `centralIsogenyCommonSemisimpleRefinement` to `π` and
   `q`. Semisimplicity of `C` comes from `hC.isSemisimple`. This gives a
   semisimple `D`, a central isogeny `p : D ⟶ C`, a homomorphism `r : D ⟶ H`
   and `p ≫ π = r ≫ q`. The proof discards the fact that `r` is a central
   isogeny. The helper then gives `a : C ⟶ H` with `a ≫ q = π`.
2. *Uniqueness.* If `b ≫ q = π`, then `b ≫ q = a ≫ q`. The cancellation
   theorem applies with the connected reductive source
   `hC.isSemisimple.isConnectedReductive` and the central isogeny `hq`, and
   gives `b = a`.

Both steps together prove `∃! a : C ⟶ H, a ≫ q = π`.

## Relation to the literature

The statement corresponds to Milne, *Algebraic Groups* (2017),
Proposition 18.8, with the codomain correction from the official errata, and
to Conrad–Gabber–Prasad, *Pseudo-reductive Groups* (2nd ed., 2015),
Corollary A.4.11(1). Milne's argument for existence assumes that the field or
the group is perfect. The Lean proof does not use that argument. It gets
existence from the published common refinement, which holds over every field,
and makes `p` invertible using the intrinsic definition of simple
connectedness. Uniqueness follows the finite-kernel argument at the end of
Milne's proof, through the published cancellation theorem.
