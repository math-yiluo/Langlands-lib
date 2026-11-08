# The `N`–`P` double cosets for the Gelfand–Graev Jacquet module

Draft by Worker 1832 for task `d7c75f29-8641-4f6e-9a08-aaa69f1db69c`. This module provides the
orbit data for the computation of the Jacquet module of the Gelfand–Graev representation
(`GelfandGraevJacquetStatement`). Restrict `c-Ind_N^G ψ` to a standard block parabolic `P`. The
Mackey filtration (`Geometric.closedSubgroupMackeyFiltration`) has one graded piece per `N`–`P`
double coset. This module picks representatives for which the open coset is easy to recognize
and every other coset is killed by the vanishing lemma (`GelfandGraevJacquetVanishing`).

## Setting

`F` is a `p`-adic field with its canonical topology, `G = GL_(n+1)(F)`, `N` is the upper
unipotent subgroup and `P = B.parabolic F.Carrier` is the standard block parabolic of a block
shape `B` of `n + 1`. `U = B.unipotentRadical F.Carrier` is its unipotent radical. `ψ` is a
nontrivial unitary additive character and `standardCharacter ψ n` is the standard character of
`N`. `MinimalRepresentatives B (BlockShape.singletons (n + 1))` is the type of minimal
permutations for `P \ G / N`, and `permutation (n + 1) F.Carrier w` is the permutation matrix
of `w`. `B.reverseMatrix F.Carrier` is the block-reversal matrix.

For a representative `r`, `orbitStabilizer N P r` is the subgroup `P ∩ r N r⁻¹` of `P`. The map
`stabilizerToInducing N P r` sends `x` in it to `r⁻¹ x r ∈ N`. The graded Mackey piece of the
coset `N r⁻¹ P` is induced from this stabilizer with the character
`x ↦ ψ_N(r⁻¹ x r)`.

## Results

- `doubleCoset_mk_inv_eq_iff`: for subgroups `H`, `K`, the double cosets `K a⁻¹ H` and `K b⁻¹ H`
  agree if and only if `H a K = H b K`.
- `gelfandGraevDoubleCoset_bijective`: the map `w ↦ N ((perm w)⁻¹)⁻¹ P`, that is
  `w ↦ N perm(w) P`, is a bijection from the minimal permutations onto `N \ G / P`.
- `gelfandGraevOrbitData`: there are `m`, an ordering
  `s : OrderedDoubleCosets N P m` of the double cosets and an index `j` such that
  - the representative `s.representative j` equals the block-reversal matrix;
  - for every `i ≠ j` there is `x` in `orbitStabilizer N P (s.representative i)` with `x ∈ U`
    and `ψ_N(stabilizerToInducing N P (s.representative i) x) ≠ 1`.

## Proofs

- `doubleCoset_mk_inv_eq_iff`: invert the equation `a⁻¹ = k b⁻¹ h` to get `a = h⁻¹ b k⁻¹`, and
  conversely.
- `gelfandGraevDoubleCoset_bijective`: Rodier's orbit classification `unipotentOrbit` says that
  `w ↦ P perm(w)⁻¹ N` is a bijection onto `P \ G / N`. Inversion of representatives turns
  `P \ G / N` into `N \ G / P` by `doubleCoset_mk_inv_eq_iff`, which gives injectivity and
  surjectivity.
- `gelfandGraevOrbitData`: the double coset space is finite by the bijection. The ordering
  `closedSubgroupOrbitOrdering` gives some ordering `s₀`, since `N` and `P` are closed.
  `OrderedDoubleCosets.classifiedRepresentatives` replaces its representatives by
  `r(w) = perm(w)⁻¹`, with an equivalence `e` from the indices to the minimal permutations, so
  that `s.representative i = perm(e i)⁻¹`. Let `j` be the index of the reversed block
  permutation `B.reversePermutation.symm`, which is minimal by
  `reversePermutation_isMinimalRepresentative`. Its representative is
  `perm(rev.symm)⁻¹ = perm(rev)`, which is the block-reversal matrix by definition.

  For `i ≠ j` the permutation `w = e i` is not `rev.symm`. The non-open witness
  `nonOpenCharacterWitness` (applied to the additive character `ψ.complex`, which is nontrivial
  because `ψ` is) gives `q ∈ N` with `w⁻¹ q w ∈ P`, with trivial Levi projection of `w⁻¹ q w`
  and with `ψ(q) ≠ 1`. Here `w` also denotes the permutation matrix. The unipotent radical is
  the kernel of the Levi projection, so `x = w⁻¹ q w` lies in `U`. It lies in
  `orbitStabilizer N P (perm(w)⁻¹)`, because `w x w⁻¹ = q ∈ N`, and its image under
  `stabilizerToInducing` is `q`. The entrywise character equals the standard character
  (`entrywiseCharacter_eq_standardCharacter`), so `ψ_N(q) ≠ 1`.

## Provenance

The classification of `P \ G / N` by minimal permutations is Rodier's (Rodier 1973; Library
`Whittaker.unipotentOrbit`). The non-open witness is the Library result
`Whittaker.nonOpenCharacterWitness`. Taking inverse representatives, so that the representative
of the open double coset `N w⁻¹ P` is the block-reversal matrix `w` itself, and packaging the
data for the Mackey filtration, are internal choices made for this computation.
