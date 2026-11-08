# Finite Fourier inversion for the weight of (4.4.18)

Internal helper for the proof of `HighlyRamifiedGammaStabilityStatement` (Jacquet–Shalika
1985, §4.4, Fourier inversion of the test function in the computation of the dual integral,
printed pages 329–330). The canonical topology, valuation and Borel structure of the p-adic
field are local instances.

- `integerLattice F m = O^(m+1)` as an additive subgroup of `F^(m+1)` (`mem_integerLattice`).
  It is open (`isOpen_integerLattice`). `isCompact_integer`: `O` is compact.
- `scaledLattice F ϖ c m = {z : ϖ^c z ∈ O^(m+1)}` (`mem_scaledLattice`). It is compact for
  `ϖ ≠ 0` (`isCompact_scaledLattice`), as the image of `O^(m+1)` under `z ↦ ϖ^(-c) z`.
- `dualWeight_support`: `Φ₂` vanishes off `scaledLattice F ϖ c m`.
- `exists_dualWeight_reps`: a finite set `T₂` of pairwise incongruent elements modulo
  `O^(m+1)` that meets the class of every point of the support of `Φ₂`. Proof:
  `exists_finset_addCosetReps` for the compact lattice and the open lattice.
- `sum_dualWeight_inversion`: for such `T₂`, if `f ≥ 1`, `ω` is trivial on `1 + 𝔭^f` and
  `ϖ^c O ⊆ 𝔭^f`, then
  `Σ_(z ∈ T₂) Φ₂(z) ∏_j a [z_(rev j) + v_j ∈ O] = a^(m+1) Φ₂(-rev v)`.
  The product is `a^(m+1)` exactly when `z ≡ -rev v` modulo `O^(m+1)`, and `sum_reps_eq` applies
  to the `O^(m+1)`-periodic `Φ₂` (`dualWeight_add`).
- `integral_dualWeight_fourier`: with `S₂(ξ) = Σ_(z ∈ T₂) Φ₂(z) ψ(Σ_k z_k ξ_k)` on integral `ξ`
  and `0` elsewhere,
  `∫ S₂(rev x) ψ(Σ_j v_j x_j) dx = η(O)^(m+1) Φ₂(-rev v)` over
  `rectangularMeasure η 1 (m+1)`, by `integral_restrictedFourier_character` and the previous
  item.
