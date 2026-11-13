# Harris's levels `K_p × K^p` and their opposite levels

Author: Worker 19.

Harris indexes the Shimura varieties of §4 of Harris (1999) by levels of the
form `K(N, m) = K(N)_p × K(m)^p ⊂ GG(A_f)`. The first factor is the `p`-adic
level `K(N)_p` (published as `SecondKindInvolution.harrisLevel` in
`HarrisDivisionLevels`). The second is a level of the prime-to-`p` finite
adelic points. This module forms such product levels for an arbitrary rational
algebra with involution and relates them to the opposite levels that index the
published CM scheme tower. It also shows that such a level is sufficiently
small as soon as its prime-to-`p` factor is, and that such prime-to-`p`
factors exist inside every level. The `p`-adic factor plays no role in this
smallness. (In Harris's case `K(N)_p` contains the similitude factor `ℤ_pˣ`
with its roots of unity, so smallness has to come from `K(m)^p`; this remark is
motivation and is not formalized.)

## Source

Harris (1999), *Galois properties of cohomological automorphic forms on
GL(n)*, Section 4, printed p. 309 (PDF p. 11): "let `K(N)_p = C_v^{N,0} ×
∏_{j>1} C^(j) × ℤ_pˣ` … and let `K(N, m) = K(N)_p × K(m)^p ⊂ GG(A_f)`". The
Shimura varieties `S_{K(N, m)}` and the constant sheaf `𝓛` used before
Proposition 4.4 are taken at these levels, with `K(m)^p` varying.

The construction of `K_p × K^p` as an inverse image under the splitting
`GG(A_f) ≅ GG(Π_{w ∣ p} ℚ_w) × GG(A_f^p)` is the formalization of Harris's
product notation. The relation to opposite levels is internal to this
Library: there the CM tower is indexed by levels of `GG(A_f)ᵐᵒᵖ`, see
`OppositePointsSplit` and the prime-to-`m` tower in
`PEL/HarrisTaylorCMPrimeToCohomology`. The smallness condition away from `p`
is Harris–Taylor's "sufficiently small" condition (the published
`AlgebraInvolution.LevelSufficientlySmall`), taken at a place not dividing
`p`.

## Declarations

All declarations are in namespace `Langlands.Shimura`.

### Opposite levels (`CompactOpenLevel`)

For a topological group `G` and a compact open level `K` of `G`:

- `CompactOpenLevel.op K` is the compact open level `Kᵐᵒᵖ` of `Gᵐᵒᵖ`, built
  with the published `opOfCompact`. `mem_op` says that `g ∈ Kᵐᵒᵖ` exactly when
  `unop g ∈ K`.
- `op_mono`, `op_le_op_iff`: `K ↦ Kᵐᵒᵖ` preserves and reflects inclusion.
  `op_injective`: it is injective.
- `transport_oppositeSplit_symm_prod_op e K K'`: for a splitting
  `e : G ≃ₜ* H × H'` and levels `K` of `H` and `K'` of `H'`, the inverse image
  of `Kᵐᵒᵖ × K'ᵐᵒᵖ` under the induced splitting `oppositeSplit e` of the
  opposite groups is `(e⁻¹ (K × K'))ᵐᵒᵖ`.

### The levels `K_p × K^p` (`AlgebraInvolution`)

Let `σ` be an algebra involution of a finite-dimensional `ℚ`-algebra `A`. Let
`p` be a prime, `v` the place of `ℚ` above `p` (a finite place whose prime
ideal contains `p`), `K_p` a level of `GG(ℚ_v) = σ.Points (FiniteCompletion ℚ v)`
and `K^p` a level of `GG(A_f^p) = σ.PrimeToPoints p`.

- `primeAdelicLevel p hp v K_p K^p` is the level `K_p × K^p` of
  `GG(A_f) = σ.FiniteAdelicPoints`. It is the inverse image, under the
  published splitting `finiteAdelicPointsSplit`, of the product of `K^p` and
  the transport of `K_p` along the published identification
  `dividingPrimePointsEquiv` of the points at the places dividing `p` with
  `GG(ℚ_v)`.
- `mem_primeAdelicLevel`: `g ∈ K_p × K^p` exactly when the component of `g`
  at `v` (published `finiteLocalMap v g`) lies in `K_p` and its prime-to-`p`
  component lies in `K^p`.
- `primeAdelicLevel_mono`: monotone in both factors.
- `primeDividingOpLevel p hp v K_p` is the opposite of the transport of `K_p`,
  a level `K₀` of `GG(Π_{w ∣ p} ℚ_w)ᵐᵒᵖ = (σ.DividingPoints p)ᵐᵒᵖ`.
  `mem_primeDividingOpLevel` describes its elements.
- `transport_finiteAdelicPointsOpSplit_symm_prod`: under the published
  opposite splitting `finiteAdelicPointsOpSplit`,
  `e⁻¹ (K₀ × K^pᵐᵒᵖ) = (K_p × K^p)ᵐᵒᵖ`. This is how `K_p × K^p` appears as a
  level of the prime-to-`p` CM tower, whose fixed factor is `K₀`.

### Smallness away from `n`

For `n : ℕ`, a level `K'` of `(σ.PrimeToPoints n)ᵐᵒᵖ` and a place `w` not
dividing `n`:

- `PrimeToLevelSmallAt n K' w`: every element of `K'` whose component at `w`
  (published `DefiniteForms.primeToLocalMap`) has finite order has trivial
  component at `w`.
- `PrimeToLevelSufficientlySmall n K'`: `PrimeToLevelSmallAt n K' w` for some
  place `w` not dividing `n`.
- `PrimeToLevelSmallAt.mono` and `PrimeToLevelSufficientlySmall.mono`: both
  conditions pass to subgroup levels.
- `primeToLevelSmallAt_op_iff`: for `K' = K^pᵐᵒᵖ` the condition is the same
  condition on the elements of `K^p`.
- `levelSmallAt_transport_prod_of_primeTo` and
  `levelSufficientlySmall_transport_prod_of_primeTo`: if `K'` satisfies the
  condition at `w`, then for every level `K₀` at the places dividing `n` the
  level `e⁻¹ (K₀ × K')` of `GG(A_f)ᵐᵒᵖ` satisfies the published
  `LevelSmallAt` at `w`, so it is sufficiently small. The proof uses the
  published identity `primeToLocalMap_finiteAdelicPointsSplit`: the component
  at `w` of a finite adelic point is the component at `w` of its prime-to-`n`
  part.
- `levelSufficientlySmall_primeAdelicLevel_op`: if `K^pᵐᵒᵖ` is sufficiently
  small away from `p`, then `(K_p × K^p)ᵐᵒᵖ` is sufficiently small, for every
  `K_p`.

### Existence of levels small away from `n`

Here `n ≠ 0`; the last three results need `A` nontrivial.

- `primeToCongruenceShrink w hq K^p`, for a place `w` not dividing `n` and
  `q ≠ 0`, is the level of `GG(A_f^n)` formed by the elements of `K^p` whose
  component at `w` lies in the principal congruence level modulo `q`. It is
  the published `DefiniteForms.smallAwayLevel`, with its published openness
  and compactness. `primeToCongruenceShrink_le`: it is contained in `K^p`.
- `primeToLevelSmallAt_primeToCongruenceShrink`: for a prime `q ≥ 3` lying in
  the prime ideal of `w`, its opposite satisfies `PrimeToLevelSmallAt` at
  `w`. The proof is the published
  `SmallLevels.congruenceLevel_torsionFree` (the congruence level modulo
  `q ≥ 3` has no nontrivial element of finite order at `w`).
- `natCast_not_mem_asIdeal_of_prime_mem`: if a prime `q` does not divide `n`
  and lies in the prime ideal of a finite place `w` of `ℚ`, then `n` does not;
  so `w` is a place not dividing `n`.
- `nonempty_primeToPoints_compactOpenLevel`: `GG(A_f^n)` has a compact open
  level. This is van Dantzig's theorem, through the published
  `exists_compact_openSubgroup_subset_points` and the published topological
  facts about `A_f^n` (`t2Space_primeToFiniteAdeles`,
  `locallyCompactSpace_primeToFiniteAdeles`,
  `totallyDisconnectedSpace_primeToFiniteAdeles`); it does not need `n ≠ 0`.
- `exists_primeToLevelSufficientlySmall_le K^p`: every level `K^p` of
  `GG(A_f^n)` contains a level `L` with `PrimeToLevelSufficientlySmall n Lᵐᵒᵖ`.
  The proof takes a prime `q > n + 2` (so `q ≥ 3` and `q ∤ n`), the place `w`
  of `ℚ` above `q` (published `existsUnique_finitePlace_natCast_mem`), and
  `L = primeToCongruenceShrink w K^p`.
- `exists_primeToLevelSufficientlySmall`: some level `K^p` of `GG(A_f^n)` has
  `PrimeToLevelSufficientlySmall n K^pᵐᵒᵖ`.

### Harris's levels (`SecondKindInvolution`)

Here `σ` is a second-kind involution of a central simple algebra `A` over the
CM field `K`, with maximal totally real subfield `E`. Also given are an
embedding `ι : F →+* K` of the imaginary quadratic field `F`, a place `𝔭` of
`F` above `v` with `ℚ_v ≅ F_𝔭`, and the division and congruence data `hdiv`,
`w₀`, `r` of `harrisLevel`.

- `splitPrimeAdelicLevel_eq_primeAdelicLevel`: the published split-prime
  level `splitPrimeAdelicLevel` (`K_p = C × ℤ_vˣ`) is, by definition,
  `primeAdelicLevel` of the published `splitPrimeLevel C`.
- `harrisPrimeAdelicLevel … K^p` is Harris's
  `K(N, m) = K(N)_p × K(m)^p`, with `K(N)_p = harrisLevel … r`. Harris's
  `C_v^{N,0}` is the case `r = ‖ϖ‖^N`.
- `mem_harrisPrimeAdelicLevel` describes its elements, via
  `mem_primeAdelicLevel`.
- `harrisDividingOpLevel` is the fixed level `K₀` attached to `K(N)_p`.
  `transport_harrisDividingOpLevel_prod` says that `e⁻¹ (K₀ × K(m)^pᵐᵒᵖ)` is
  `K(N, m)ᵐᵒᵖ`.

## Scope

The module is about levels only. The CM schemes and the cohomology of
constant sheaves at these levels are in `PEL/HarrisTaylorCMHarrisLevels`.
Harris's specific prime-to-`p` levels `K(m)^p`, defined through an
identification `GG(A_f^p) ≅ GJ(A_f^p)`, are not constructed. Every level
`K^p` that is sufficiently small at one place not dividing `p` is allowed in
their place, and such levels exist inside every level of `GG(A_f^p)`
(`exists_primeToLevelSufficientlySmall_le`).
