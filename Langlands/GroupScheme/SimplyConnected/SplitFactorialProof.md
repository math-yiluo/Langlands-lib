# Proof: the coordinate ring of a split simply connected group is factorial

This module proves the Library statement
`Langlands.GroupScheme.SplitSimplyConnectedFactorialStatement.{u}` (module
`Langlands.GroupScheme.SimplyConnected.SplitFactorialStatement`) as

```
theorem splitSimplyConnectedFactorial : SplitSimplyConnectedFactorialStatement.{u}
```

For every field `k : Type u` and every group scheme `G` over `Spec k` with
`IsSimplyConnected G` and `HasSplitMaximalTorus G`, the ring `Γ(G.X.left, ⊤)` is
an integral domain and a unique factorization monoid. The statement is used
unchanged. The proof uses only the axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Sources and route

The theorem is Popov 1974, Proposition 1 and its Corollary, over an
algebraically closed field. Over an arbitrary field, for split groups, it
follows from Milne 2017, Corollary 18.24. The Library statement's Markdown
records the source comparison. The Lean proof follows the Popov-style "one
chart" route, with the following steps.

1. The big cell `Ω` of a coordinate split structure is a factorial chart of
   `A = Γ(G.X.left, ⊤)`.
2. For each simple root `a`, consider the left translate `u_a(1) · Ω`. Inside
   it, the complement of `Ω` lies in the divisor `1 + y_{-a} = 0`, where
   `y_{-a}` is the coordinate of the opposite root group. This divisor gives a
   discrete valuation of the function field. The torus character of the
   fundamental weight `ω_a` is a uniformizer there and a unit at the other
   boundary divisors.
3. Every height-one prime of `A` comes from `Ω` or is one of these boundary
   primes (exhaustion).
4. The commutative-algebra criterion `uniqueFactorizationMonoid_of_chart`
   (module `CommutativeAlgebra/ChartUniqueFactorization`) then gives unique
   factorization.

The implementation departs from this route in two places:

- The boundary charts are translates by the root-group points `u_a(1)`, not by
  Weyl representatives `n_a`. These translates need only the rank-one relation
  `u_a(x) u_{-a}(y) = u_{-a}(y/d) a∨(d) u_a(x/d)` with `d = 1 + xy`.
- The exhaustion uses neither the rational Bruhat decomposition nor relative
  Weyl generation. It uses a stabilizer argument (modules `FactorialStabilizer`,
  `FactorialExhaustion` and `FactorialAssembly`). Let `y` be the point of a
  height-one prime `q` of `A`, outside `Ω` and outside every translated chart
  `u_a(1) · Ω`, and let `Z = closure {y}`.
  - `Z` is disjoint from `Ω`, and separately from every translated chart. A
    point of `Z` in one of these open sets is a specialization of `y`, so `y`
    would lie in that set too.
  - Every irreducible closed subset of `G ∖ Ω` containing `Z` is contained in
    `Z` (`subset_closure_of_height_eq_one`, which does not itself assume that
    `Z` avoids `Ω`). Since `Z` lies in `G ∖ Ω` by the previous point, `Z` is
    maximal among irreducible closed subsets of `G ∖ Ω`. Maximality is relative
    to `Ω` alone, not to the complement of the union of all charts. The generic
    point of a larger such set has a prime contained in `q`. That prime is
    nonzero, since the set misses the nonempty `Ω`, so it equals `q`.
  - Let `H` be a simple root group `u_a`, its opposite `u_{-a}` or the torus.
    For every point `h` of `H` and every point `z` of `Z`, the translate
    `h · z` avoids `Ω`. For `u_{-a}` and the torus, this holds because they
    keep `Ω` stable under left multiplication and `Z` avoids `Ω`. For `u_a`, it
    uses that `Z` avoids both `Ω` and `u_a(1) · Ω`. So the closure of the image
    of `H × Z` under the action map is an irreducible closed subset of `G ∖ Ω`
    containing `Z`. By maximality it lies in `Z`. Hence `Z` is stable under
    these subgroups, so under all root groups and the torus, so under every
    point of `Ω`.
  - That is impossible. Let `κ` be the residue field of a point `y₀ ∈ Z`, and
    let `g : G_κ → G` be the projection from the base change. Since `G_κ` is
    irreducible, there is a nonempty open `U` of `G_κ` on which both `g` and
    `g · y₀` land in `Ω`. On `U`, the translate `g · y₀` then lands in
    `Z ∩ Ω = ∅`.

The proof works over any field, for groups with a split maximal torus.

## This module

`nonempty_cellData` builds the coordinate split data `CellData k G` (module
`FactorialCellData`) of a connected reductive group with a split maximal torus:

- the split torus `T ≅ splitTorus (Spec k) I` (definition of `IsSplitTorus`)
  gives a coordinate torus `i`, which is maximal by `IsMaximalTorus.iso_comp`
  and fibrewise maximal by `IsMaximalTorus.isFibrewiseMaximalTorus`;
- `IsConnectedReductive.isReductive` gives reductivity over `Spec k`;
- `localSplitFibrewiseRootDatumExistence` gives a finite reduced coordinate
  root datum `P` with `IsFibrewiseRootDatumOf`;
- `SplitExistence.nonempty_base_int` gives a base of `P`;
- `localSplitRootGroup` gives root parametrizations, Weyl-normalized at the
  simple roots.

`splitSimplyConnectedFactorial` then collects the ring facts:

- `G` is affine, smooth and connected (fields of `IsConnectedReductive`);
- `G.X.left` is integral (`CoverPreimage.isIntegral_of_smooth_connected`);
- `Γ(G.X.left, ⊤)` is Noetherian (`BorelExistence.isNoetherianRing_globalSections`);
- `Γ(G.X.left, ⊤)` is integrally closed: every stalk of the smooth `k`-scheme is
  an integrally closed domain (`AlgebraicGeometry.Smooth.isDomain_and_isIntegrallyClosed_stalk`),
  and `EtaleNormalLocallyIrreducible.isDomain_isIntegrallyClosed_sections`
  passes this to the sections over the affine open `⊤`.

It takes fundamental weights from `CellData.exists_fundamentalWeights` (module
`FactorialWeights`, which uses simple connectedness) and enumerations of the
negative and positive roots, and applies
`CellData.uniqueFactorizationMonoid_of_weights` (module `FactorialAssembly`).
The domain conjunct is the instance for the integral scheme.

## Helper modules

The proof consists of this entry module and the following helper modules,
each with its own Markdown:

- `Langlands/CommutativeAlgebra/ChartUniqueFactorization`:
  the unique-factorization criterion from one factorial chart.
- `Langlands/CommutativeAlgebra/ChartPrimeValuation`: the valuation of a prime
  element of a factorial chart.
- `Langlands/AlgebraicGeometry/FunctionFieldChart`: sections over open
  immersions as subalgebras of the function field, and the chart property.
- `Langlands/GroupScheme/SimplyConnected/FactorialCellRing`: the coordinate ring
  `k[v, w, t^{±1}]` of the cell source, its factoriality and the isomorphism of
  its spectrum with the cell source.
- `.../FactorialCellData`: the coordinate split data, the big-cell charts and
  the directly spanned root subgroups.
- `.../FactorialRankOne`: root combinatorics and the rank-one translation of a
  cell point.
- `.../FactorialBoundaryChart`: the translated charts and the torus characters
  across the boundary.
- `.../FactorialStabilizer`: stabilizers of closed sets under left translation.
- `.../FactorialExhaustion`: exhaustion of the complement of the big cell.
- `.../FactorialWeights`: fundamental weights of a simply connected group.
- `.../FactorialAssembly`: the application of the criterion.
