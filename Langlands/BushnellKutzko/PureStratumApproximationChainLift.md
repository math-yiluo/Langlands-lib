# Chains over an extension field, viewed over the base field

Source context: Bushnell–Kutzko, *The admissible dual of GL(N) via compact open subgroups* (1993), `bushnell-kutzko-1993-admissible-dual-gln`. (1.2.1), printed p. 24 (PDF p. 36), identifies `𝔬_F`-lattice chains normalized by `Eˣ` with `𝔬_E`-lattice chains. (1.4.13), printed p. 39 (PDF p. 51), compares critical exponents of an element of `E` on two such chains. These are the tools for moving a simple stratum between chains in the proof of (2.4.5), printed pp. 67–69. The statements below are derived lemmas in the Library's indexed-chain model.

## Lifting an `𝔬_E`-chain

Throughout, `F` is a nonarchimedean local field, `E/F` a finite extension acting on `V`, and `subfieldIntegers F E` the integral closure `𝔬_E`.

- `isLattice_restrictScalars`: an `𝔬_E`-lattice of `V` is an `𝔬_F`-lattice. It is finitely generated over `𝔬_F` because `𝔬_E` is finite over `𝔬_F`. Its `F`-span is closed under `E`, since a base scalar moves any element of `E` into `𝔬_E` (`exists_smul_mem_subfieldIntegers`); hence the span is `V`.
- `uniformizer_smul_mem_iff`, `zpow_uniformizer_smul_mem_iff`, `integerUnit_smul_mem_iff`, `units_smul_mem_iff`: for an `𝔬_E`-chain `M` with period `e'`, multiplication by `u ϖ_E^k` (`u` a unit of `𝔬_E`) carries `M_i` onto `M_{i+k e'}`.
- `baseUniformizer_smul_mem_iff`: the base uniformizer `π_F = u ϖ_E^{e(E|F)}` (`baseUniformizer_factorization`) carries `M_i` onto `M_{i+e(E|F) e'}`.
- `liftChain M` is the `𝔬_F`-lattice chain with the same lattices (`coe_liftChain_lattice`). Its periodicity is the previous item, with positive exponent by `subfieldRamificationIndex_pos'`.
- `liftChain_period`: its period is `e(E|F)` times the period of `M` (`LatticeChain.period_unique`).
- `liftChain_normalized`: `Eˣ` normalizes it, by the unit factorization `subfieldUnit_factorization`.
- `mem_liftChain_endFiltration_iff`: an `E`-linear endomorphism lies in a filtration step of the lifted chain exactly when it lies in the same step of `M`.
- `coe_liftChain_subfieldChain_lattice`: lifting the published `subfieldChain` of an `E`-normalized chain `𝓛` returns the lattices of `𝓛`.

## Valuations and critical exponents on two normalized chains

- `valuation_subfieldEmbedding`: on a chain normalized by `E`, the valuation of `a = u ϖ_E^m` is `m` times the shift of `ϖ_E`. It is read from the Library's `valuation_eq_shift` and `fieldShift_eq_mul_of_factorization`.
- `exists_valuation_of_normalized`: if `v_𝓛(a) = −n`, then `v_{𝓛'}(a) = −n'` with `n' e(𝓛) = n e(𝓛')`. The proof uses `fieldShift_uniformizer_mul_ramification`, which says that the shift of `ϖ_E` times `e(E|F)` is the period.
- `normalizingUnits_regular`: the regular action of a generator of `E` on `E` generates an algebra whose units normalize any chain on the line `E` normalized by `E`.
- `criticalExponent_subfieldEmbedding_eq` (BK93 (1.4.13)(ii)): let `β` generate `E` and let `𝓛` be normalized by `E`. Then `k₀(β,𝓛)` is the critical exponent of the regular action of `β` on the line chain `subfieldBasisChain (Basis.singleton Unit E)` (the powers of `𝔭_E`), multiplied by the shift `d` of `ϖ_E` on `𝓛`; the value `⊥` is preserved. The proof chooses a relative splitting basis (`exists_relSplits_basis`) and scaled coordinates (`scaledLatticeCoordinates_of_normalizing`), and applies `diagonalCriticalExponent` to the diagonal of the regular action, which is the action of `β` (`diagonal_mulLeft`).
- `criticalExponent_lt_of_normalized`: suppose `k₀(β,𝓛) < −r` and `ρ e(𝓛) ≤ r e(𝓛')`. Then `k₀(β,𝓛') < −ρ`. Both critical exponents are multiples of the same line exponent by the shifts `d` and `d'`, and `d e(E|F) = e(𝓛)`, `d' e(E|F) = e(𝓛')`. The inequality follows by integer arithmetic.
