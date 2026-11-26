# Two chains normalized by one field

Source context: Bushnell–Kutzko, *The admissible dual of GL(N) via compact open subgroups* (1993), `bushnell-kutzko-1993-admissible-dual-gln`. (1.2.10), printed p. 27 (PDF p. 39), computes `𝔓^n = 𝔄(E) ⊗ 𝔔^n` in a `(W,E)`-decomposition, so that the filtration of an `E`-normalized order is determined by its intersection with `B = End_E(V)`. (1.3.12) and the remark after it, printed p. 31 (PDF p. 43), give `s(L) = L ∩ B` for the lattices built from such filtrations, including intersections of steps of two orders. The proof of (2.4.5), printed p. 68 (PDF p. 80), uses both for two hereditary orders normalized by `E`. This module proves them in the forms used there, in the Library's chain model, with a common relative splitting basis in place of a common `(W,E)`-decomposition.

## Common relative splitting basis

`exists_relSplits_basis_both` says that two `𝔬_F`-lattice chains `𝓛`, `𝓛'` normalized by `E` have a common relative splitting basis: an `E`-basis `w` of `V` with `RelSplits 𝓛 w` and `RelSplits 𝓛' w`. The proof gives `E` its spectral local-field structure (`LocalField.FiniteExtension`). It transports both `subfieldChain`s to chains over `𝒪[E]` along `subfieldIntegerEquiv` (`LatticeChain.transfer`), and then to coordinates `Fin d → E`. There it applies `LatticeChain.exists_basis_splits_both` and transports the basis back. Splitting for chains over `𝒪[E]` with the same lattices is relative splitting.

## Blocks

For an `E`-basis `w`:

- `elementaryE w c j l` is the `E`-linear map `v ↦ (w.repr v l · c) w_j`. `blockEntry_elementaryE` computes its blocks: multiplication by `c` in position `(j,l)`, zero elsewhere.
- `lineIncl_comp_blockEntry`: the summand of `assembleBlocks` in position `(j,l)` is the sandwich `ε_j x ε_l` by the `E`-linear idempotents `ε_j = elementaryE w 1 j j`. `sum_elementaryE_one`: `∑ ε_j = 1`.
- `mulLeft_zpow_mem_iff`: multiplication by `ϖ_E^k` lies in step `m` of the line chain `subfieldBasisChain (Basis.singleton Unit E)` exactly when `m ≤ k`. Its uniformizer shift is one (`uniformizerShift_eq_one_of_cyclic`), and `subfieldEmbedding_unit_mem_iff` applies.
- `exists_blockLevels`: for a relative splitting basis of an `E`-normalized chain, `x ∈ 𝔓^t(𝓛)` exactly when each block of `x` lies in step `⌈(t + p_l − p_j)/d⌉` of the line chain, for some `d > 0` and offsets `p`. This combines `scaledLatticeCoordinates_of_normalizing` with `blockFiltration`.

## The two comparisons

- `endFiltration_le_of_restrict_le` (BK93 (1.2.10)): if every `E`-linear element of `𝔓^t(𝓛)` lies in `𝔓^{t'}(𝓛')`, then `𝔓^t(𝓛) ⊆ 𝔓^{t'}(𝓛')`. With a common relative splitting basis, test the hypothesis on `elementaryE w (ϖ_E^λ) j l`, where `λ` is the block level of `𝓛`. This shows that each block level of `𝓛'` is at most that of `𝓛`. The block description then gives the inclusion for all endomorphisms.
- `exists_corestriction_eq_of_mem` (BK93 (1.3.12)): let `s` be a tame corestriction, `b ∈ 𝔓^t(𝓛)` and `s(b) ∈ 𝔓^{t'}(𝓛')`. Then some `p ∈ 𝔓^t(𝓛) ∩ 𝔓^{t'}(𝓛')` has `s(p) = s(b)`. By T1 (`tameCorestriction`) choose `Z ∈ 𝔓^{t'}(𝓛')` with `s(Z) = s(b)`. In each block take the block of `b` where the level of `𝓛'` is at most that of `𝓛`, and the block of `Z` otherwise. The assembled `p` lies in both steps by the block description. Since `s` is a `B`-bimodule map and the `ε_j` are `E`-linear, `s(ε_j X ε_l) = ε_j s(X) ε_l`, so `s(p) = ∑ ε_j s(b) ε_l = s(b)`.
