# Moy's reduction with a compatible chain

Sources: C. J. Bushnell, *Hereditary orders, Gauss sums and supercuspidal representations of GL_N* (1987), `bushnell-1987-hereditary-orders-gauss-sums`, Theorem 1, printed p. 192, with its proof, printed pp. 194–195. Bushnell–Kutzko, *The admissible dual of GL(N) via compact open subgroups* (1993), `bushnell-kutzko-1993-admissible-dual-gln`, quote it as (2.3.1), printed p. 57 (PDF p. 69). After (2.3.1) they note that the new order can be chosen so that the pair of orders satisfies (1.1.9), printed p. 23.

The Library's `LatticeChain.exists_latticeChain_of_pow_mem` (module `MoyReduction`) gives, for `x ∈ 𝔓^j(𝓛)` whose coset `x + 𝔓^{j+1}(𝓛)` contains an element `y` with `y^n ∈ 𝔓^{nj+1}(𝓛)`, a chain `𝓜` and `j'` with `x + 𝔓^{j+1}(𝓛) ⊆ 𝔓^{j'}(𝓜)` and `j e(𝓜) < j' e(𝓛)`. This module records in addition that every lattice of `𝓜` is sandwiched between two consecutive lattices of `𝓛` (`LatticeChain.IsSandwiched`). In particular every lattice of `𝓜` is comparable with every lattice of `𝓛`, and the incidence relation of Remark (ii) after (1.1.9), printed p. 24, holds: `𝔓(𝓛) ⊆ 𝔄(𝓜)`.

## Results

- `LatticeChain.exists_latticeChain_shift_sandwiched` is `LatticeChain.exists_latticeChain_shift` with the extra conclusion `∀ t, ∃ p, 𝓛.IsSandwiched p (𝓜.lattice t)`. The proof is that of `exists_latticeChain_shift`. There the lattices of `𝓜` are exactly the set `C = {ϖ^k J^l(L_q)}`, and every member of `C` is sandwiched (`hCsw` in the proof).
- `LatticeChain.exists_latticeChain_of_pow_mem_sandwiched` is `exists_latticeChain_of_pow_mem` with the same extra conclusion, by the same proof applied to the coset-image operator.
- `LatticeChain.exists_latticeChain_of_isNilpotent_sandwiched` is the case of a nilpotent element of the coset.

The proofs repeat those of the module `MoyReduction` without change, apart from carrying the sandwich property. That module's Markdown describes the construction.
