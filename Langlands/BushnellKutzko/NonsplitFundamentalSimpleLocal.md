# The semisimplicity criterion over the integers of a local field

Module `Langlands.BushnellKutzko.NonsplitFundamentalSimpleLocal`, namespace
`Langlands.BushnellKutzko.NonsplitSimple`. It imports `NonsplitFundamentalSimpleResidue` and
`NonsplitRefinementProof`.

## Statement

`nonsplitSimpleCriterion_integer S : S.NonsplitSimpleCriterion` holds for every nonarchimedean
local field `F` (any universe), every `F`-vector space `V` and every stratum
`S = [𝓛, n, r, b]` over `𝔬_F` (`Stratum 𝒪[F] F V`). Spelled out: if `1 ≤ n` and `S` is nonsplit
fundamental, then `S` is equivalent to a simple stratum `T` with `T.chain = S.chain`,
`T.n = S.n` and `T.r = S.r` exactly when the residue centralizer `S.residueCentralizer` is a
semisimple ring. The hypothesis `1 ≤ n` is not used. A lattice chain forces `V` to be
finite-dimensional (`LatticeChain.finiteDimensional`).

## The data of a nonsplit fundamental stratum

`NonsplitData S` records a uniformizer `ϖ`, shift parameters `N` for `(e(𝓛), −n)`, a unit
`B = b` translating the chain by `−n`, a monic `P ∈ 𝔬_F[X]` with unit constant coefficient and
irreducible reduction, and `m > 0` with `P(y)^m ∈ 𝔓`. Here `y` is `residualOrder`, equal to
`ϖ^{−k} b^h` (`coe_residualOrder_eq_smul`).

`exists_nonsplitData` constructs these data from `S.IsNonsplit`, with `g = gcd(e, |n|)`, so that
`y` is the element `Stratum.fundamentalElement` of the definition of nonsplit strata and `P`
lifts its residual polynomial. It follows the first steps of
the proof of `PureApproximation.nonsplitRefinement` (module `NonsplitRefinementProof`). It uses
the lemmas proved there: `NonsplitRefinement.aeval_pow_mem_one` (Cayley–Hamilton for an integral
characteristic polynomial), `LatticeChain.exists_isNilpotent_add_of_pow_mem_endFiltration` (which
excludes `p = X`), `NonsplitRefinement.exists_unit_of_aeval_pow_mem` (`y` is a unit of `𝔄`) and
`NonsplitRefinement.shifts_of_pow` (`b` translates the chain).

## The two directions

- `aeval_mem_of_simple`: if `S` is equivalent to a simple stratum `T` on the same chain and
  levels, then `P(y) ∈ 𝔓`. Let `c = T.b`. Equivalence gives `b − c ∈ 𝔓^{1−n}`, hence
  `c^h − b^h ∈ 𝔓^{−hn+1}` (`CriticalDerived.SymbolEq.pow`), and `y_c = ϖ^{−k} c^h` satisfies
  `y_c ∈ 𝔄` and `y_c − y ∈ 𝔓`. Integral polynomials respect congruence modulo `𝔓`
  (`aeval_sub_mem_of_sub_mem`, through the layer actions), so `P(y_c)^m ∈ 𝔓` and
  `P(y_c) − P(y) ∈ 𝔓`. The element `w = P(y_c)` lies in the field `F[c]`. If `w ≠ 0`, purity of
  `T` and `normalizingUnits_of_isField` make `w` a unit translating the chain by some `s`. From
  `w ∈ 𝔄` we get `s ≥ 0`, and from `w^m ∈ 𝔓` we get `ms ≥ 1`, using
  `CriticalDerived.Shifts.not_mem_succ`. So `s ≥ 1` and `w ∈ 𝔓`. In every case `P(y) ∈ 𝔓`.
- `exists_simple_of_aeval_mem`: if `P(y) ∈ 𝔓`, the cyclic-lift theorem
  `CriticalDerived.exists_simple_cyclic_lift`, applied on the chain `𝓛` itself to `B`, `N` and
  `P`, gives `c ≡ b (mod 𝔓^{1−n})` with `F[c]` a field whose units normalize `𝓛` and
  `k₀(c, 𝓛) ≤ −n`. Then `T = [𝓛, n, n−1, c]` has `v_𝓛(c) = −n`
  (`LatticeChain.valuation_eq_of_mem_of_notMem`). It is simple because `−n < 1 − n`, and it has
  the same coset as `S`.

Combining these with `isSemisimpleRing_of_aeval_mem` and `aeval_mem_of_isSemisimpleRing` (module
`NonsplitFundamentalSimpleResidue`) proves `nonsplitSimpleCriterion_integer`: both sides of the
criterion are equivalent to `P(y) ∈ 𝔓`.

## Provenance

This is Bushnell–Kutzko, *The admissible dual of GL(N) via compact open subgroups* (1993),
(2.4.13), printed p. 75 (PDF p. 87), literature ID `bushnell-kutzko-1993-admissible-dual-gln`,
over `𝔬_F`. The source proves it in §2.5, printed pp. 76–83 (PDF pp. 88–95), by conjugating to a
standard form (2.5.11) and computing there (2.5.8)–(2.5.10). BK93 derives the "only if" direction
of (2.5.8) from the critical exponent: the kernel of `x ↦ βxβ^{−1} − x` on `𝔄/𝔓` is
`𝔅 + 𝔓`. The Lean proof uses neither the standard form nor that kernel computation. It uses only
that the units of `F[c]` translate the chain, and it uses the Library's cyclic lift for the
converse.
