# Proof of the semisimplicity criterion for nonsplit fundamental strata (BK93 (2.4.13))

Module `Langlands.BushnellKutzko.NonsplitFundamentalSimpleProof`.
`Langlands.BushnellKutzko.nonsplitFundamentalSimple` proves the unchanged Library proposition
`Langlands.BushnellKutzko.NonsplitFundamentalSimpleStatement` (module
`NonsplitFundamentalSimpleStatement`) at its universes `uF`, `uE`, `uV`:

```lean
theorem Langlands.BushnellKutzko.nonsplitFundamentalSimple :
    NonsplitFundamentalSimpleStatement.{uF, uE, uV}
```

## What is proved

For every nonarchimedean local field `F`, both clauses of the statement hold. For every stratum
`S = [𝔄, n, n−1, b]` with `1 ≤ n` that is nonsplit fundamental (`Stratum.IsNonsplit`), `S` is
equivalent to a simple stratum with the same lattice chain and the same integers `n` and `r`
exactly when the residue centralizer
`ℛ = {x ∈ 𝔄/𝔓 : xb ≡ bx (mod 𝔓^{1−n})}` (`Stratum.residueCentralizer`) is a semisimple ring.
The first clause concerns strata over `𝒪[F]` in `F`-vector spaces. The second concerns strata
over `subfieldIntegers F E` in `E`-vector spaces, for every finite extension `E/F`.

Source: Bushnell–Kutzko, *The admissible dual of GL(N) via compact open subgroups* (1993),
(2.4.13), printed p. 75 (PDF p. 87), literature ID `bushnell-kutzko-1993-admissible-dual-gln`,
with the source proof in §2.5, printed pp. 76–83 (PDF pp. 88–95). The extension clause is the
form used for derived strata in Bushnell–Kutzko, *Simple types in GL(N): computing conjugacy
classes* (1994), (5.5)–(5.6), printed p. 133, literature ID
`bushnell-kutzko-1994-simple-types-conjugacy-classes`.

## Implemented proof

1. **The clause over `𝒪[F]`** is `NonsplitSimple.nonsplitSimpleCriterion_integer` (module
   `NonsplitFundamentalSimpleLocal`). Let `y = ϖ^{−k} b^h` be the element of
   `Stratum.fundamentalElement`, with `e(𝓛) = hg`, `−n = gk`, `g = gcd(e, |n|)`, and let `P` be a
   monic lift of the irreducible residual polynomial. Then `b` is a unit translating the chain
   by `−n` and `P(y)^m ∈ 𝔓` (`exists_nonsplitData`). Both sides of the criterion are equivalent
   to `P(y) ∈ 𝔓`:
   - a simple stratum `[𝓛, n, n−1, c]` equivalent to `S` gives `P(y) ∈ 𝔓`, because
     `P(ϖ^{−k} c^h)` lies in the field `F[c]`, whose nonzero elements translate the chain
     (`aeval_mem_of_simple`);
   - `P(y) ∈ 𝔓` gives such a simple stratum by the Library's cyclic-lift theorem
     `CriticalDerived.exists_simple_cyclic_lift` on the same chain (`exists_simple_of_aeval_mem`);
   - `ℛ` is isomorphic to a product of centralizers of the action of `y` on the layers
     `L_j/L_{j+1}`, `0 ≤ j < g` (`residueCentralizerEquiv`, module
     `NonsplitFundamentalSimpleResidue`). These are semisimple when `P(y) ∈ 𝔓`, because the
     layers become vector spaces over the field `k_F[X]/(P̄)`. Conversely, if `ℛ` is
     semisimple, the central nilpotent element `P(y)` of each factor vanishes, so `P(y) ∈ 𝔓`.
2. **The clause over `subfieldIntegers F E`.** The proof installs the spectral local-field
   structure of `E`: `LocalField.FiniteExtension.normedField`, `valuativeRel` and
   `isLocalField`. The integral closure is then isomorphic to `𝒪[E]` by
   `subfieldIntegerEquiv F E`, which is the identity on elements of `E`. The stratum `S` over
   `subfieldIntegers F E` is transported to a stratum `S'` over `𝒪[E]` with the same lattices,
   integers and element (`NonsplitSimple.transportStratum`, module
   `NonsplitFundamentalSimpleTransport`). For `S'` the first clause applies with `E` as the local
   field. `NonsplitRefinement.mem_of_le_valuation` gives `b ∈ 𝔓^{−n}`, and
   `NonsplitSimple.nonsplitSimpleCriterion_of_transport` carries the criterion back to `S`.

The hypothesis `1 ≤ n` is not used. The Lean proof does not follow the source's route through
the standard form of (2.5.7) and (2.5.11). It replaces the block-matrix computations
(2.5.8)–(2.5.10) by the layer actions of `𝔄/𝔓` and transport along the translation
`b^u ϖ^v` of shift `g`.

## Modules

- `NonsplitFundamentalSimpleAlgebra`: centralizers of endomorphisms annihilated by a maximal
  ideal of `R[X]` are semisimple; central nilpotents in semisimple rings vanish.
- `NonsplitFundamentalSimpleLayers`: the action of `𝔄/𝔓` on the layers and families extended
  along a translation.
- `NonsplitFundamentalSimpleResidue`: the residue centralizer as a product of layer centralizers
  and the two semisimplicity implications.
- `NonsplitFundamentalSimpleLocal`: the criterion over `𝒪[F]`.
- `NonsplitFundamentalSimpleTransport`: change of the integer ring of a stratum.
