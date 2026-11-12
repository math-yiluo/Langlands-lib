# Cocenter characters of the centralizer of a cocharacter

Authors: Worker 187.

The module `Langlands.GroupScheme.Rational.DynamicCentralizerCocenterComparison`
(namespace `Langlands.GroupScheme.DynamicCentralizerCocenterComparison`) computes the
characters of the cocenter of the centralizer of a cocharacter of a maximal torus,
after base change to a field splitting the torus. It is an internal helper for
`Langlands.GroupScheme.leviCocenterKernelGeneration`. It specializes the published
comparison `characterLattice.cocenter_coweight_comparison_of_structuralInputs`
(module `Rational.LeviCocenterRootModelAssembly`) to dynamic centralizers and
transports it along base change.

Mathematically: let `L = Z_G(ζ)` contain the maximal torus `T`, and let `R = L/D(L)` be
its cocenter. Pulling back along `T → L → R` identifies the characters of `R` with
the characters of `T` that vanish on the coroots of `L`. Those are the coroots of the
roots vanishing on `ζ`.

## Results

The module adds two local instances: base change along any `Spec K ⟶ Spec k` keeps a
group scheme affine (`baseChangeAffine`) and locally of finite type
(`baseChangeFiniteType`).

- `isClosedSubgroup`: if `G` is affine, every representative `l : L ⟶ G` of the
  dynamic centralizer of a cocharacter `groupHom ζ ≫ amb` is a closed subgroup.
  Proof: `l` is isomorphic over `G` to the affine centralizer representative
  `Dynamic.Affine.centralizerHom`, which is a closed subgroup
  (`Dynamic.Affine.isClosedSubgroup_centralizerHom`). Apply
  `IsClosedSubgroup.iso_comp`.
- `cocenter_isSplitTorus`: let `L` be connected reductive with a maximal torus
  `tL : T ⟶ L` whose base change to `E` is split. Let `e : D ⟶ L` be its derived
  subgroup and `r : L ⟶ R` an fppf quotient by the range of `e`. Then `R_E` is a
  split torus. Proof: `cocenterQuotientExistence` gives one such quotient `R₀` that
  splits over every field splitting a maximal torus of `L`. Both quotient maps are
  quasi-compact: `L` is affine and group schemes over a field are separated
  (`fieldSeparated`). So `FppfQuotientComparison.iso` identifies `R` with `R₀`, and
  `IsSplitTorus.of_iso` transfers splitness.
- `splitComparison` (split case): over a field `K`, let `amb : T ⟶ G` be a closed
  subgroup with split `T` and root datum `P`. Let `l : L ⟶ G` represent the
  centralizer of `ζ`, with `L` connected reductive. Let `tL : T ⟶ L` be a maximal
  torus with `tL ≫ l = amb`, and `r : L ⟶ R` the cocenter quotient with `R` split.
  Then `characterLattice.precompose (tL ≫ r)` is injective. Its range is the set of
  characters `χ` with `⟨χ, coroot p⟩ = 0` for every root `p` with
  `P.root' p ζ = 0`. Proof: `rootDatumExistence` gives a root datum of `tL`, and
  `relativeRoots_centralizer_factor` identifies its roots with the roots of `amb`
  vanishing on `ζ`. Then `cocenter_coweight_comparison_of_structuralInputs` applies,
  with the published structural inputs `rootDatumExistence`,
  `derivedSubgroupSemisimple`, `derivedMaximalTorusProductSurjectivity` and
  `derivedMaximalTorusIntersection`.
- `comparison`: let `G` be connected reductive over `k`, `amb : T ⟶ G` a maximal
  torus, and `E/k` an algebraic extension with `T_E` split and `P` a root datum of
  `amb_E`. Let `l : L ⟶ G` represent the centralizer of `ζ`, with
  `tL ≫ l = amb`, derived subgroup `e`, and cocenter quotient `r : L ⟶ R`. Then
  `R_E` is split, and `characterLattice.baseChangePullback k E (tL ≫ r)` is
  injective with range the characters of `T_E` annihilating the coroots of the roots
  vanishing on `bc(ζ)`. Proof:
  1. `l` is a closed subgroup (`isClosedSubgroup`), so `L` is connected reductive
     (`dynamicCentralizerReductive`) and `tL` is a maximal torus of `L`
     (`IsMaximalTorus.of_comp`). Hence `R_E` is split (`cocenter_isSplitTorus`).
  2. Base change to `E` preserves the hypotheses. `L_E` is connected reductive
     (`IsConnectedReductive.baseChange_of_algebraicExtension`), and `(tL)_E` is a
     maximal torus (`maximalTorusBaseChange`). `e_E` is the derived subgroup
     (`derivedSubgroup_baseChange_eq_of_field`), `r_E` is an fppf quotient by its
     range (`IsFppfQuotient.baseChange`, `SubgroupFunctor.range_baseChangeHom`), and
     `l_E` represents the centralizer of `bc(ζ)`
     (`Dynamic.isRepresentedBy_centralizer_baseChange`).
  3. `splitComparison` over `E` gives the result for `precompose ((tL)_E ≫ r_E)`.
     This is `baseChangePullback k E (tL ≫ r)`, since base change is a functor.
