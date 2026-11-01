# Unipotent volume of a compact set along a diagonal translate

Module `Langlands.Representation.RankinSelberg.UnipotentDiagonalVolume`.

Let `F` be a `p`-adic field with its canonical topological data
`T = F.canonicalTopologicalData`, and write `|x| = T.normalizedAbs x`,
`m = n + 1`, `N = upperUnipotent m F.Carrier` with `du = unipotentHaar F.Carrier n`
(mass one on the integral unipotent subgroup). The topology, valuation and
local-field structure on `F.Carrier` are the canonical ones, installed as local
instances. `N` carries any σ-algebra that is Borel for its topology.

## Statement

`Langlands.RankinSelberg.unipotentHaar_mul_diagonal_le (n : ℕ) (L) (hL : IsCompact L)`:
for a compact set `L` of `m × m` matrices over `F.Carrier` there are a unit `r`, a
real constant `C` and exponents `e : Fin m → ℕ` such that, for every
`a : Fin m → F.Carrierˣ`,

1. if `u · diag(a) ∈ L` for some `u ∈ N`, then `|a_i| ≤ |r|` for every `i`; and
2. `du {u ∈ N | u · diag(a) ∈ L} ≤ ENNReal.ofReal (C · ∏_i |a_i|⁻¹ ^ e_i)`.

The bound holds for every `a`. When the set is empty, the left side is `0`.

This is internal derived content. It is the volume estimate that the planned
reduction of the coefficient rationality statement (C) to the coefficient torus
expansion needs, in the exact form Worker 249 requested. It is the standard step
behind the convergence of Whittaker integrals for Schwartz–Bruhat data: the support
of `a ↦ ∫_N Φ(u diag(a)) du` is bounded in every `|a_i|`, and its size is
controlled by a monomial in `|a_i|⁻¹`. No literature statement is formalized here.

The witnesses in the proof are explicit:
`r = ϖ^(-M)` for the Library uniformizer unit `ϖ` and an `M` with `R < q^M`,
where `R` bounds `∑_{i,j} |M_ij|` on `L` and `q` is the residue cardinality;
`D = ∑_{i<j} (j - i)`, `e_i = D` for every `i`, and `C = |r|^(m·D)`.

## Helper lemmas (namespace `Langlands.RankinSelberg.UnipotentDiagonalVolume`)

- `normalizedAbs_units_pow`, `normalizedAbs_units_prod`:
  the normalized absolute value of a power and finite product of units,
  for any `T : F.TopologicalData`.
- The inverse identity reuses the published
  `Langlands.Whittaker.JPSDilationAssembly.normalizedAbs_units_inv` from
  [`JPSDilationAssemblyProof`](../Whittaker/JPSDilationAssemblyProof.md).
- `diagonalConj_entry` (any field): the `(i, j)` entry of `diagonalConj β u` is
  `β_i β_j⁻¹ u_ij`.

## Proof

The sum of `|M_ij|` is continuous on the matrix space, so it has an upper bound
`R` on the compact set `L`. Hence every entry of every matrix in `L` has
absolute value at most `R`, and `R ≤ |r| = q^M`
(`LocalFactor.PadicAbelian.uniformizerUnit_zpow_abs`).

Part 1: the `(i, i)` entry of `u · diag(a)` is `a_i`, because `u` has unit diagonal.

Part 2: if no `u` satisfies `u · diag(a) ∈ L`, the set is empty. Otherwise part 1
gives `|a_k| / |r| ≤ 1` for all `k`. Put `t = ∏_k a_k r⁻¹`, so `x = |t|` satisfies
`0 < x ≤ |a_j| / |r| ≤ 1` for every `j`. Put `β_i = t^(n - i)`, so that
`β_i β_j⁻¹ = t^(j - i)` for `i ≤ j`. If `u · diag(a) ∈ L`, then the entry
`(i, j)` with `i < j` of `diagonalConj β u` satisfies

```text
|t^(j-i) u_ij| ≤ x |u_ij| ≤ |u_ij a_j| / |r| ≤ R / |r| ≤ 1.
```

The diagonal entries are `1` and the entries below the diagonal are `0`, so
`diagonalConj β u` is integral. By
`Unramified.MinusculeCosets.unipotent_mem_integralSubgroup` it lies in the
integral unipotent subgroup `unipotentIntegralOpen F.Carrier n`. So the set is
contained in `diagonalConj β ⁻¹' unipotentIntegralOpen`.

That preimage has volume equal to the inverse singleton-block Levi modulus of
`β`. This uses the published `diagonalConj_map`, which scales `du` under
`diagonalConj β`, together with `unipotentHaar_integral` (mass one on the integral
subgroup). The σ-algebra on `N` is identified with the Borel one only inside this
step (`BorelSpace.measurable_eq`). By `singleton_modulus_real` the modulus is
`∏_{i<j} |β_i / β_j| = x^D`. Finally

```text
(x^D)⁻¹ = ∏_k (|a_k|⁻¹ |r|)^D = |r|^(m·D) ∏_k |a_k|⁻¹^D,
```

which is the claimed bound with `C = |r|^(m·D)` and `e_k = D`.
