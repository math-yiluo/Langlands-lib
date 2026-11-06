# Proof of uniqueness of block decompositions

`Langlands.WeilDeligneRepresentation.Blocks.decompositionUniqueness.{uG, uV, uW}`
proves the Library proposition
`Langlands.WeilDeligneRepresentation.Blocks.DecompositionUniqueness.{uG, uV, uW}`
from `Langlands.WeilDeligne.BlockStatements`. Its type is exactly that
proposition, for arbitrary universes `uG` (group), `uV` and `uW` (carriers of
the two families of Weil factors). The proof uses only the standard axioms
`propext`, `Classical.choice` and `Quot.sound`.

## Statement proved

Let \(G\) be a group, \(\nu : G \to \mathbb{C}^\times\) a character, and let
\(d_1,\dots,d_k\) and \(d'_1,\dots,d'_l\) be block data with irreducible Weil
factors \(\sigma_i\), \(\sigma'_c\) and lengths \(m_i, m'_c \ge 1\). The pair
\(\bigoplus_i \sigma_i \otimes \mathrm{Sp}(m_i)\) is equivalent to
\(\bigoplus_c \sigma'_c \otimes \mathrm{Sp}(m'_c)\) (as Weil–Deligne pairs, by a
linear equivalence intertwining the actions and the monodromies) if and only if
there is a bijection \(e : \mathrm{Fin}\,k \simeq \mathrm{Fin}\,l\) with
\(m_i = m'_{e(i)}\) and \(\sigma_i \simeq \sigma'_{e(i)}\) for every \(i\).
The two families may live in different carrier universes.

## Reverse implication

The reverse implication is Worker 1687's Library lemma
`Blocks.decompositionEquiv_of_matching` from
`Langlands.WeilDeligne.BlockEquivalences`. It tensors each Weil-factor
equivalence with the identity on the special block, takes the componentwise
direct sum, and reindexes along \(e\). The main theorem applies it at
\(K = \mathbb{C}\).

## Forward implication (`DecompositionUniquenessProof.forward`)

All auxiliary declarations live in the namespace
`Langlands.WeilDeligneRepresentation.Blocks.DecompositionUniquenessProof`.

1. **The invariant.** For representations \(\pi\) on \(P\) and \(\rho\) on
   \(V\) and an endomorphism \(N\) of \(V\), `layer N j` is
   \(\ker N \cap \operatorname{im} N^j\). `homInto π ρ S` is the subspace of
   intertwiners \(\pi \to \rho\) with image in \(S\), and
   `count π ρ N j` is \(\dim_{\mathbb{C}}\) of `homInto π ρ (layer N j)`.
   `count_congr` shows the count is unchanged under an equivalence of
   representations that commutes with the two endomorphisms. It uses
   postcomposition (`postcomp`, `homIntoCongr`) and the identity
   \(e(N^j v) = N'^j(e v)\) (`equiv_pow_apply`, `mem_layer_congr`).

2. **Additivity.** For a finite direct sum with componentwise monodromy
   `DirectSum.lmap N`, an element lies in the layer exactly when each component
   does (`mem_layer_lmap`, via `lmap_pow`, `DirectSum.ker_lmap` and
   `DirectSum.range_lmap`). Intertwiners into a direct sum with image in such a
   subspace correspond to families of intertwiners into the summands
   (`homIntoDirectSum`, built from `DirectSum.component` and
   `DirectSum.linearEquivFunOnFintype`). Hence `count_directSum`: the count of
   the sum is the sum of the counts.

3. **Coordinate model of a block.** `piAction ν σ m` acts on
   \(\mathrm{Fin}\,m \to U\) by \((g \cdot y)_k = \nu(g)^k\,\sigma(g)(y_k)\).
   `piShift U m` is the shift \((Ny)_k = y_{k-1}\) for \(k > 0\) and
   \((Ny)_0 = 0\). `blockEquivPi` identifies the Library block
   `block ν σ m` (that is, \(\sigma \otimes (\mathrm{Fin}\,m \to \mathbb{C})\))
   with this model. It is Mathlib's `TensorProduct.piScalarRight`, sending
   \(x \otimes f\) to \(k \mapsto f_k\,x\). `blockEquivPi_monodromy` shows that
   it carries the block monodromy (`block_monodromy_tmul`, the raising operator
   on the special factor) to `piShift`. Both identities are checked on pure
   tensors.

4. **Layers of one block.** `piShift_pow_apply` gives
   \((N^j z)_k = z_{k-j}\) if \(j \le k\) and \(0\) otherwise. For
   \(m = n + 1\): if \(j \le n\), the layer is \(\ker N\), the vectors
   supported on the last coordinate \(n\) (`layer_piShift_of_le`). If
   \(j > n\), the layer is zero (`layer_piShift_of_lt`). Projection to and
   insertion at the last coordinate (`topEquiv`) identify intertwiners into
   \(\ker N\) with intertwiners
   \(\pi \to \nu^n \otimes \sigma\) (`Langlands.twist (ν ^ n) σ`). Hence
   `count_block` and `count_pair`: a block of length \(m\) contributes
   \(\dim \operatorname{Hom}_G(\pi, \nu^{m-1}\sigma)\) to layer \(j\) when
   \(j < m\), and \(0\) otherwise.

5. **Difference of consecutive layers.** Summing over the blocks,
   `count_succ` gives
   \[
   \mathrm{count}_j = \mathrm{count}_{j+1} + \sum_{i : m_i = j+1}
     \dim \operatorname{Hom}_G(\pi, \nu^j \sigma_i).
   \]

6. **Multiplicities.** Take \(\pi = \nu^j \tau\) with \(\tau\) irreducible.
   The Library's `Langlands.twistIntertwiningEquiv` cancels the common twist, so
   each summand is \(\dim \operatorname{Hom}_G(\tau, \sigma_i)\). Schur's lemma
   over \(\mathbb{C}\) (`finrank_intertwiningMap_irreducible`, from Mathlib's
   `Representation.IsIrreducible.finrank_intertwiningMap_self`, transported
   across carrier universes by postcomposition) makes this \(1\) if
   \(\tau \simeq \sigma_i\) and \(0\) otherwise. So the sum is
   `mult d τ j`, the number of \(i\) with \(m_i = j + 1\) and
   \(\tau \simeq \sigma_i\) (`sum_finrank_eq_mult`). Applying `count_congr` to
   the given equivalence at layers \(j\) and \(j+1\) gives `mult_eq_of_equiv`:
   `mult d τ j = mult d' τ j` for every irreducible \(\tau\) in any carrier
   universe.

7. **Matching counts.** Worker 1687's `Blocks.BlockDataMatch a b` (from
   `Langlands.WeilDeligne.BlockMatching`) means equal lengths and an
   equivalence of Weil factors. `card_match_eq_mult` shows that the number of
   \(i\) with `BlockDataMatch (d i) b` is `mult d σ_b (m_b - 1)`, where
   \(\sigma_b\) and \(m_b\) are the factor and length of \(b\). The two
   conditions differ only in the direction of the factor equivalence, which
   is inverted. With step 6, `card_match_eq_of_equiv`
   shows that both families have equally many blocks matching any datum
   \(b\) with irreducible factor, in any carrier universe.

8. **Conclusion.** `forward` applies Worker 1687's finite matching lemma
   `Blocks.matching_of_class_counts` from `Langlands.WeilDeligne.BlockMatching`.
   It needs these equal counts for every datum \(b\) of either family, so
   step 7 is applied with \(b = d_a\) and with \(b = d'_c\). The lemma
   quotients the tagged union of the two index sets by `BlockDataMatch` and
   matches the fibers with `Equiv.ofFiberEquiv`. The result is a bijection
   \(e\) with \(m_i = m'_{e(i)}\) and \(\sigma_i \simeq \sigma'_{e(i)}\).

## Main theorem

`decompositionUniqueness` combines `forward` (step 8) with
`decompositionEquiv_of_matching`. Irreducibility of the Weil factors is used
only in the forward implication, through Schur's lemma.
