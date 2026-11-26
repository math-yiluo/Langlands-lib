# Assembling finitely many operators into an `ℓ²` product

Module `Langlands.Analysis.Meromorphic.PiOperatorAssembly`. For a complex normed space `B`, a
finite index type `Ω` and complex normed spaces `Fib ω`:

- `piAssemble L : B →L[ℂ] PiLp 2 Fib` is `x ↦ (L ω x)_ω` for continuous linear maps
  `L ω : B →L[ℂ] Fib ω` (`piAssemble_apply`). `piInclude ω : Fib ω →L[ℂ] PiLp 2 Fib` is the
  inclusion of one coordinate, and `piAssemble_eq_sum`: `piAssemble L = ∑_ω piInclude ω ∘ L ω`.
- `isCompactOperator_piAssemble`: if every `L ω` is compact, so is `piAssemble L` (a finite sum of
  compact operators, by induction over the index set).
- `isEmbedding_piAssemble`: if `0 ≤ C` and `‖x‖ ≤ C ∑_ω ‖L ω x‖` for every `x`, then `piAssemble L`
  is a topological embedding. Each `‖L ω x‖` is at most the `ℓ²` norm of `piAssemble L x`, so
  `‖x‖ ≤ C |Ω| ‖piAssemble L x‖`; the map is antilipschitz, hence a uniform embedding.

Weak holomorphy (`IsHolomorphicOperatorFamilyOn`, Bernstein–Lapid §3.2) of operator families on a
complex manifold `M`, on a set `U`:

- `IsHolomorphicOperatorFamilyOn.piAssemble`: the assembly `s ↦ piAssemble (L · s)` of weakly
  holomorphic families is weakly holomorphic (a continuous linear form on `PiLp 2 Fib` composed
  with `piAssemble_eq_sum` is a finite sum of forms on the coordinates);
- `isHolomorphicOperatorFamilyOn_const`: constant families;
- `IsHolomorphicOperatorFamilyOn.clm_comp` and `.comp_clm`: composition with a fixed continuous
  linear map on the left or on the right;
- `isHolomorphicOperatorFamilyOn_sum_smul`: `s ↦ ∑_{j ∈ t} c_j(s) • K_j` for fixed operators `K_j`
  and coefficients `c_j` that are complex differentiable on `U`;
- `IsHolomorphicOperatorFamilyOn.add`: sums of two families.

## Provenance

These are elementary facts used to assemble the operator families of the Fredholm criterion of
Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer. Math. Soc. 37
(2024), §3.2 (analytic families of operators, p. 193) and its application in §7.6
(pp. 219–220), where the operators `μ_s` and `ν_s` take values in a finite direct sum of Hilbert
spaces (literature id `bernstein-lapid-2024-meromorphic-continuation-eisenstein`).
