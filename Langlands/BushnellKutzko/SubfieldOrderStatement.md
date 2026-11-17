# The hereditary order `𝔅 = 𝔄 ∩ B` (Bushnell–Kutzko 1993, (1.2.2)–(1.2.4), p. 25)

Source: C. J. Bushnell and P. C. Kutzko, *The admissible dual of GL(N) via compact open
subgroups*, Annals of Math. Studies 129 (1993), `bushnell-kutzko-1993-admissible-dual-gln`,
(1.2.2)–(1.2.3) and Proposition (1.2.4) with its proof, printed p. 25 (PDF p. 37; PDF page =
printed page + 12).

`SubfieldOrderStatement : Prop` is an unproved statement. A later `lean.proof@1` task will
prove it. It uses `Langlands.BushnellKutzko.LatticeChain`, `...UnitFiltration` and
`...SubfieldIntegers`.

## Quantifiers and hypothesis

The quantifiers are those of `SubfieldNormalizerStatement`: a nonarchimedean local field
`F : Type u`, an `F`-vector space `V : Type v`, a field `E : Type w` with
`[Algebra F E] [Module E V] [IsScalarTower F E V]`, and an `𝔬_F`-lattice chain
`𝓛 : LatticeChain 𝒪[F] F V`, in independent universes. The hypothesis is condition (i) of
(1.2.1): `subfieldUnits F E V a ∈ 𝓛.stabilizer` for every `a ∈ E^×`, i.e. `E^× ⊆ 𝔎(𝔄)`. BK93
assumes "the equivalent conditions of (1.2.1)". The task asks for S5 "under the conditions of
S4", and condition (i) is the one used.

Notation: `A = Module.End F V`, `𝔄 = 𝓛.order`, `𝔓^n = 𝓛.endFiltration n`,
`𝔬_E = subfieldIntegers F E`, `e(E|F) = subfieldRamificationIndex F E`. Following (1.2.2),
`B = End_E(V) = Module.End E V`, the `A`-centralizer of `E`. It is viewed inside `A` through
`LinearMap.restrictScalars F`, which is injective and whose image is the set of `F`-linear maps
commuting with the action of `E`.

## Conclusion

There is an `𝔬_E`-lattice chain `𝓛' : LatticeChain 𝔬_E E V` in the `E`-vector space `V` such
that:

1. **`𝓛'` has the same lattices as `𝓛`**: `(𝓛'.lattice i : Set V) = 𝓛.lattice i` for all `i`.
   This is BK93's statement that `𝓛` itself is an `𝔬_E`-lattice chain ((1.2.1)(ii)). Since a
   lattice chain is determined by its lattices, `𝓛'` is unique.
2. **`𝔅 = 𝔄 ∩ B` is the hereditary `𝔬_E`-order `𝔄(𝓛')`** ((1.2.3), (1.2.4)). For every
   `y ∈ B`: `y ∈ 𝓛'.order` if and only if `y ∈ 𝔄` (as an element of `A`). So
   `𝓛'.order = End^0_{𝔬_E}(𝓛')` is `𝔄 ∩ B`, and it is hereditary in the sense of
   `IsHereditaryOrder` (the lattice-chain description).
3. **`𝔓^n ∩ B = End^n_{𝔬_E}(𝓛')` for every `n ∈ ℤ`** ((1.2.4) and its proof). For every
   `y ∈ B`: `y ∈ 𝓛'.endFiltration n` if and only if `y ∈ 𝔓^n`.
4. **`𝔔^n = End^n_{𝔬_E}(𝓛')` are the powers of the radical `𝔔` of `𝔅`** ((1.2.3)–(1.2.4)).
   This is stated as `End^m_{𝔬_E}(𝓛') End^n_{𝔬_E}(𝓛') = End^{m+n}_{𝔬_E}(𝓛')` for all
   `m, n ∈ ℤ` (product of `𝔬_E`-submodules of `B`), together with: for `y ∈ 𝔅`,
   `y ∈ Ring.jacobson 𝔅` if and only if `y ∈ End^1_{𝔬_E}(𝓛')`. With 3, this gives BK93's
   `𝔔 = 𝔓 ∩ B` is the Jacobson radical of `𝔅` and `𝔔^n = 𝔓^n ∩ B` for all `n ∈ ℤ`. Here
   `𝔔^n` for negative `n` is the power of the invertible fractional ideal `𝔔`, as in
   `RadicalFiltrationStatement`.
5. **`e(𝔄|𝔬_F) = e(E|F) · e(𝔅|𝔬_E)`** ((1.2.4)): `𝓛.period = e(E|F) * 𝓛'.period`. BK93
   writes `e' = e(𝔅) = e(𝔅|𝔬_E) = e(𝔄|𝔬_F)/e(E|F)`. Here `e'` is the integer of (1.2.1)(ii),
   which is the `𝔬_E`-period of `𝓛'` by `LatticeChain.period_unique`. The periods of the
   chains are BK93's `e(𝔄|𝔬_F)` and `e(𝔅|𝔬_E)` (p. 21: "the period `e` of `𝓛` is also a
   function of `𝔄`").

## Relation to the task

The task's S5 asks that `𝔅 = 𝔄 ∩ B` be the hereditary `𝔬_E`-order of the `𝔬_E`-lattice chain
`𝓛` (parts 1–2), that `𝔓^n ∩ B` be its `n`-th radical power for every `n` (parts 3–4), and that
`e(𝔄|𝔬_F) = e(E|F) · e(𝔅|𝔬_E)` (part 5). The `𝔬_E`-lattice chain is an object of the generic
structure `LatticeChain (subfieldIntegers F E) E V`. Its periodicity ideal is
`Ring.jacobson 𝔬_E = 𝔭_E = subfieldMaximalIdeal F E`.
