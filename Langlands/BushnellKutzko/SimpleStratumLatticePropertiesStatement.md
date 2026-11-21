# The lattice properties of a simple stratum (U1)

Source: C. J. Bushnell and P. C. Kutzko, *The admissible dual of GL(N) via compact open subgroups* (1993), (3.1.9)–(3.1.13) and the remarks after (3.1.9) and (3.1.10), printed pp. 91–94 (PDF pp. 103–106). The choice-dependent construction starts in (3.1.7)–(3.1.8), printed p. 90 (PDF p. 102).

`SimpleStratumLatticePropertiesStatement` is the following conjunction, for every simple `[𝔄,n,0,β]` in the endomorphism algebra of a finite-dimensional vector space over a nonarchimedean local field. The hereditary order is represented by its lattice chain. Field and vector-space universes are independent, and all choices are defining sequences starting at their indicated element.

1. The two constructed lattices are independent of that choice.
2. Both are `𝔬_F`-lattices, each underlying a unital `𝔬_F`-subalgebra; `𝔅_β ⊆ ℌ ⊆ 𝔍 ⊆ 𝔄`. Their nonnegative layers are two-sided ideals in their respective rings, with `ℌ^k ⊆ 𝔍^k`. The internal ideal predicate expresses containment and both multiplication inequalities in the ambient algebra.
3. For a simple equivalent `[𝔄,n,r,γ]` at the finite critical depth `r` (necessarily `r<n`), the layers coincide with those of `γ` for `k ≥ ⌊r/2⌋+1` for `ℌ` and `k ≥ ⌊(r+1)/2⌋` for `𝔍`.
4. For every integer `m` and natural `k`, `𝔔_β^m` commutes under submodule product with each of `ℌ^k` and `𝔍^k`; both layers are invariant under conjugation by `𝔎(𝔅_β)`. The published `centralizerLattice` realizes all fractional powers `𝔔_β^m = 𝔓^m ∩ B_β`.
5. `𝔔_β 𝔍^k ⊆ ℌ^{k+1}` for all `k ≥ 0`, `𝔍^k 𝔍^l ⊆ ℌ^{k+l}` for `k,l ≥ 1`, and `ℌ^k` is a two-sided ideal in `𝔍` for `k ≥ 1`.
6. For equivalent simple data at depth `t<r` (an integer, not restricted to be nonnegative), the filtered lattices agree for `k ≥ max(0,t+1−⌊(r+1)/2⌋)` for `ℌ` and `k ≥ max(0,t−⌊r/2⌋)` for `𝔍`. Equivalence at the common depth is expressed by the difference lying in `𝔓^{−t}`; the scalar case `r=∞` uses both lower bounds equal to zero.

This is a proposition definition, not a proof of any of the clauses.
