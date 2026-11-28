# Proof: irreducible smooth representations of `Dˣ` are finite-dimensional

Namespace `Langlands.JacquetLanglands`.

The theorem `irreducibleDivisionUnitsFiniteDimensional` proves exactly the
published proposition `IrreducibleDivisionUnitsFiniteDimensionalStatement` of
the module
`Langlands.JacquetLanglands.CorrespondenceInputs.DivisionUnitsFiniteDimensional`.
Both universe parameters are free: `u`, the universe of `F` and `D`, and `uW`,
the universe of the carrier `W`.
The theorem holds for every nonarchimedean local field `F`, of any
characteristic, and every finite-dimensional central division algebra `D` over
`F` with its module topology. The proof does not use the hypothesis
`Algebra.IsCentral F D`.

## Route

The proof uses compactness of `Dˣ` modulo the central powers of an element of
`F` whose valuation generates the value group, together with Schur's lemma in
countable dimension. The argument in the
statement's Markdown passes to the normal subgroups `1 + 𝔭_D^k`. The Lean proof
does not: it uses only one nonzero vector `w` and an open subgroup `U` fixing
it. It never constructs the valuation ring of `D` or a reduced norm.

1. **Lifting a generator of the value group** (`exists_valuation_zpow_eq`). Mathlib's
   `Mathlib.NumberTheory.LocalField.Basic` provides the instance
   `IsCyclic (ValueGroupWithZero F)ˣ`. The valuation `valuation F` is
   surjective, so a generator of this group is `valuation F ϖ` for some
   `ϖ ≠ 0`. Every nonzero `a ∈ F` then satisfies
   `valuation F (ϖ ^ m) = valuation F a` for some `m : ℤ`. The generator may
   lie above or below `1`, so `ϖ` is a uniformizer or the inverse of one; the
   proof uses all integer powers and needs neither orientation.

2. **Continuity of inversion on `D`** (`continuousInv₀_division`). Let `b` be
   the basis `Module.finBasis F D` and `e` the coordinate homeomorphism
   `coordinateHomeomorph F D b`. Let `M x` be the matrix of left
   multiplication by `x` (`Algebra.leftMulMatrix b`). For `x ≠ 0` the inverse
   is `x⁻¹ = e⁻¹ ((M x)⁻¹ *ᵥ e 1)`. Near a nonzero `x`, the matrix inverse
   `(M y)⁻¹ = (det M y)⁻¹ • adj (M y)` is continuous, since `det M x ≠ 0`.
   This gives `ContinuousInv₀ D`. By Mathlib's `Units.isEmbedding_val₀`, the
   inclusion `Dˣ → D` is then a topological embedding for the units topology.

3. **A compact fundamental set for scaling** (`exists_isCompact_zpow_smul_mem`).
   Let `T ⊆ F^n` be the set of coordinate vectors all of whose entries have
   valuation `≤ 1`, at least one of them exactly `1`. Let `C = e⁻¹(T)`.
   - `C` is compact. It is a closed subset of the product of the compact
     unit balls (`IsNonarchimedeanLocalField.isCompact_closedBall`). The
     condition "some coordinate has valuation `1`" is closed, because
     `valuation F` is continuous for Mathlib's `WithZeroTopology`
     (`IsValuativeTopology.continuous_valuation`).
   - `0 ∉ C`.
   - Let `x ≠ 0`, and let `y_j` be a coordinate of `e x` of maximal
     valuation. Then `y_j ≠ 0`. Choose `m` with
     `valuation F (ϖ ^ m) = valuation F y_j` by step 1. Then
     `ϖ ^ (-m) • x ∈ C`.

4. **A cover of `Dˣ`** (`exists_central_finite_cover`). Let `U` be an open
   subgroup of `Dˣ`. By step 2 the units lying in `C` form a compact subset
   of `Dˣ`. Mathlib's `compact_covered_by_mul_left_translates` covers it by
   finitely many translates `{h | t * h ∈ U}` with `t ∈ S₀`.
   - Let `ζ_m` be the unit `algebraMap F D (ϖ ^ m)`. It is central, by
     `Algebra.commutes`.
   - By step 3, every `g ∈ Dˣ` has `ζ_m * g ∈ C` for some `m`. Hence
     `t * (ζ_m * g) ∈ U` for some `t ∈ S₀`, and
     `g = ζ_m⁻¹ * t⁻¹ * (t * (ζ_m * g))`.
   - This gives `Dˣ = Z S U` with `Z = {ζ_m⁻¹ : m ∈ ℤ}` countable and central,
     and `S = {t⁻¹ : t ∈ S₀}` finite.

5. **The representation-theoretic step**
   (`finiteDimensional_of_central_finite_cover`, for an arbitrary group `G`).
   Let `ρ` be irreducible, let `w ≠ 0` be fixed by a subgroup `U`, and suppose
   `G = Z S U` with `Z` a countable set of central elements and `S` finite.
   - The orbit `{ρ g w}` lies in `{ρ z (ρ s w) : z ∈ Z, s ∈ S}`, so it is
     countable.
   - The orbit spans `W` (the Library's `span_range_orbit_eq_top`). Hence
     `Module.rank ℂ W ≤ ℵ₀`.
   - For central `z`, `ρ z` is an intertwining endomorphism. The Library's
     `countableDimensionalSchur` makes it a scalar `c_z`.
   - So every `ρ g w = c_z • ρ s w` lies in the span of the finitely many
     vectors `ρ s w`, `s ∈ S`. That span is `W`, which is therefore
     finite-dimensional (`Module.finite_def`, `Submodule.fg_span`).

6. **The theorem.** An irreducible `ρ'` is a simple module, so `W` is
   nontrivial; choose `w ≠ 0`. Smoothness (`IsSmooth`) gives an open subgroup
   `K` with `w ∈ fixedVectors ρ' K`, that is, `ρ' u w = w` for all `u ∈ K`
   (`Representation.mem_invariants`). Steps 4 and 5 with `U = K` conclude.

## Declarations

- `finiteDimensional_of_central_finite_cover`: step 5, for any group `G` and
  any complex vector space `W`.
- `exists_valuation_zpow_eq`: step 1.
- `continuousInv₀_division`: step 2, for a finite-dimensional division ring
  `D` over `F` with its module topology.
- `exists_isCompact_zpow_smul_mem`: step 3.
- `exists_central_finite_cover`: step 4.
- `irreducibleDivisionUnitsFiniteDimensional`: the theorem, of type
  `IrreducibleDivisionUnitsFiniteDimensionalStatement.{u, uW}`.

The helper lemmas are implementation results of this proof. Their hypotheses
are those displayed in their Lean statements; none of them assumes centrality
of `D`.
