# One square-integrable coefficient suffices, without assumed admissibility

Author: Worker 4988.

## Target

`Langlands.Renard.CompactRepresentation.singleCoefficientSquareIntegrability` proves
`SingleCoefficientSquareIntegrabilityStatement.{u, v}`
(`Langlands/Representation/MatrixCoefficient/SingleCoefficientSquareIntegrabilityStatement.lean`).
The setting is a group `G : Type u` with a Hausdorff, locally compact, totally disconnected
topological group structure. `μ` is a Haar measure on `G ⧸ Z(G)` that is also right
invariant. `π : SmoothRep.{0, u, v} ℂ G` is irreducible, and `c` is a unitary central
character of `π`. Suppose that for some smooth functional `ℓ` and some vector `x`, the
coefficient `matrixCoefficient π ℓ x` is nonzero and `c.coefficientNorm ℓ x` (the function
`g Z(G) ↦ ‖ℓ(π(g) x)‖`) is in `L²(μ)`. Then `c.coefficientNorm m y` is in `L²(μ)` for every
smooth functional `m` and every vector `y`. This is the Remark of Renard IV.3.2. Neither the
hypothesis nor the conclusion assumes admissibility.

## Route

The proof first shows that `π` is admissible (`isAdmissible_of_memLp`). The published
admissible criterion `squareIntegrableCoefficientCriterion`
(`SquareIntegrableCoefficientCriterionProof.lean`) then gives the conclusion. Renard leaves
the Remark to the reader; this route is Worker 4988's. Its dimension bound comes from the
trace argument that Worker 5099 described for countable groups, made independent of
countability by the bounded Schur lemma (`Langlands/Analysis/BoundedSchur.lean`) and
`Langlands.Analysis.finiteDimensional_of_tracial'` (`Langlands/Analysis/TracialFiniteness.lean`).

## Declarations in this file

All are in the namespace `Langlands.Renard.CompactRepresentation.SingleCoefficient`, except
the main theorem.

### The subgroup `K · Z(G)` and the character `ψ`

`K` is a subgroup of `G` and `χ : Z(G) →* ℂˣ`.

* `centerMul K`: the subgroup `K · Z(G) = {k z | k ∈ K, z ∈ Z(G)}`. `mem_centerMul_iff`,
  `center_le_centerMul`, `le_centerMul`.
* `centerPart j`: a central element `z` with `j = k * z` for some `k ∈ K` (chosen).
  `exists_eq_mul_centerPart`.
* Hypothesis `hKχ`: `χ z = 1` for every central `z ∈ K`. Under it, `char_centerPart` shows
  that `χ z` does not depend on the decomposition `j = k z`.
* `centerChar χ hKχ : centerMul K →* ℂ`: the character `k z ↦ χ z` (`centerChar_apply`,
  `centerChar_eq`). `centerChar_of_mem`: it is `1` on `K`.

### Topology

* `isOpen_centerMul`: `K · Z(G)` is open if `K` is open.
* `centralImage_centerMul_subset`: the image of `K · Z(G)` in `G ⧸ Z(G)` lies in the image
  of `K`. `centralImage_centerMul_ne_top`: so it has finite Haar measure if `K` is compact.
* `finite_quotient_heckeSub`: for compact open `K`, each Hecke subgroup
  `TwistedCoset.heckeSub K g` (`K ∩ g K g⁻¹`) has finite index in `K`.
* `exists_compact_le_ker`: for `χ` with open kernel and an open subgroup `K₀`, there is a
  compact open subgroup `K ⊆ K₀` with `χ z = 1` for every central `z ∈ K`. It uses van
  Dantzig's theorem (`Topology.LocallyProfiniteProof.vanDantzig`).

### Square-integrable coefficient vectors

* `integrableVectors hρ c μ ℓ`: the subspace of vectors `x` with
  `c.coefficientNorm ℓ x ∈ L²(μ)`. The coefficient of a sum is bounded pointwise by the
  sum of the coefficients.
* `memLp_coefficientNorm_rho`: this subspace is stable under `π(g)`, by right invariance
  of `μ`.
* `memLp_coefficientNorm_of_irreducible`: if `π` is irreducible and one nonzero `x` has
  `c.coefficientNorm ℓ x ∈ L²(μ)`, then every vector has this property for the same `ℓ`.
  The subspace contains the orbit of `x`, which spans `V` (`span_range_orbit_eq_top`).

### The coefficient map on `K`-fixed vectors

From here on `K` is an open subgroup and `hKχ` holds for `χ = c.character`.
`ψ = centerChar c.character hKχ` and `J = K · Z(G)`.

* `norm_centerChar`: `‖ψ j‖ = 1`.
* `coefficient_mul`: for `y` fixed by `K` and `j ∈ J`,
  `ℓ(π(g j) y) = ℓ(π(g) y) ψ(j)`.
* `tsum_coefficient_ne_top`: for such `y` with square-integrable coefficient,
  `∑' α : G ⧸ J, ‖ℓ(π(α.out) y)‖ₑ² ≠ ∞`.
* `coeffMap μ c K hKχ ℓ hall`: assuming `hall` (every vector has square-integrable
  coefficient for `ℓ`), the linear map `y ↦ (α ↦ ℓ(π(α.out) y))` from the `K`-fixed vectors
  to `TwistedCoset.L2 J = ℓ²(G ⧸ J)`. `coeffMap_apply`.
* `lift_coeffMap`: `TwistedCoset.lift J ψ (coeffMap y) = (g ↦ ℓ(π(g) y))`.
* `coeffMap_injective`: if `π` is irreducible and `ℓ ≠ 0`, `coeffMap` is injective.

### Hecke operators on coefficients

Now `K` is also compact and `π` is smooth (`hρ`).

* `averageFixed hρ K hKc`: the average over `K` (`Compact.averageMap`), as a map onto the
  `K`-fixed vectors. `coe_averageFixed`, `averageFixed_of_mem` (it fixes `K`-fixed vectors).
* `hecke_coeffMap`: for the bounded Hecke operator `TwistedCoset.hecke g hb` of
  `HeckeOperator.lean`, `hecke g (coeffMap y) = coeffMap (averageFixed (π(g) y))`.

### Finite dimensionality and admissibility

* `finiteDimensional_fixedVectors`: let `π` be smooth and irreducible, `μ` a right
  invariant Haar measure, `K` compact open with `hKχ`, `ℓ ≠ 0`, and `hall`. Then the
  `K`-fixed vectors form a finite-dimensional space.
* `isAdmissible_of_memLp`: let `π` be smooth and irreducible with unitary central character
  `c`, with `G` Hausdorff, locally compact and totally disconnected. If
  `matrixCoefficient ρ ℓ x ≠ 0` and `c.coefficientNorm ℓ x ∈ L²(μ)`, then `π` is admissible
  (`IsAdmissible ρ`).
* `singleCoefficientSquareIntegrability`: the target.

## The hypotheses of the tracial finiteness theorem

`finiteDimensional_fixedVectors` applies `Langlands.Analysis.finiteDimensional_of_tracial'`
with the following data.

* `H = TwistedCoset.L2 J = ℓ²(G ⧸ J)`, with `J = K · Z(G)`.
* `S = TwistedCoset.translates hψ`, the left translations `translate h`, `h ∈ G`. So
  `N = StarSubalgebra.centralizer ℂ S` is the commutant of the left translations.
* `ξ = TwistedCoset.xi`, the `ψ`-twisted indicator of `J`. It exists because `ψ` is defined,
  which needs `hKχ`: `χ` is trivial on `K ∩ Z(G)`. `exists_compact_le_ker` provides such a
  `K` inside any open subgroup `K₀`, so the condition costs nothing for admissibility.
* `hnorm` (traciality, `‖x ξ‖ = ‖star x ξ‖` for `x ∈ N`):
  `TwistedCoset.norm_apply_xi_eq_norm_star_apply_xi` (`TwistedCosetSpace.lean`). For
  `x ∈ N`, the coordinate of `star x ξ` at `α` has the norm of `lift (x ξ)` at `α.out⁻¹`
  (`TwistedCoset.norm_star_apply_xi_apply`). So both squared norms are sums of the same
  function, over the representatives and over their inverses. These sums agree by
  `CentralCoset.tsum_out_eq_tsum_out_inv`, which uses the left and right invariance of `μ`
  instead of inversion invariance. This needs `μ (image of J) ≠ ∞`, from
  `centralImage_centerMul_ne_top`.
* `hsep` (`x ξ = 0 → x = 0` for `x ∈ N`): `TwistedCoset.eq_zero_of_apply_xi`. The
  translates of `ξ` span a dense subspace, and `x` commutes with them.
* `V = LinearMap.range A` with `A = coeffMap`: the coefficient functions of `K`-fixed
  vectors. `V` need not be closed.
* `htrans`: for `u ≠ 0` and `w` in `V`, some `b ∈ N` preserves `V` and maps `u` to `w`.
  Write `u = A y` and `w = A y'`. Then `y ≠ 0`, and by irreducibility `y'` lies in the span
  of the orbit `π(g) y`. For `v = π(g) y`, the Hecke operator `b = hecke g` lies in `N`
  (`TwistedCoset.hecke_mem_centralizer`). It maps `V` into `V`, and
  `b (A y) = A (averageFixed v)` (`hecke_coeffMap`). Linear combinations of these operators
  handle the span (the induction `key`). Since `y'` is `K`-fixed, `averageFixed y' = y'`,
  so `b u = w`.

`finiteDimensional_of_tracial'` takes `B` to be the elements of `N` that preserve `V`.
Inside `TracialFiniteness.lean`:

* `B ⊆ N`, and `B` preserves `V`, by construction.
* `B` acts transitively on `V` (from `htrans`).
* Every `ℂ`-linear endomorphism of `V` that commutes with `B` is a scalar. This is the
  bounded Schur lemma `exists_eq_smul_id_of_commutesOn`. It needs no countability. If a
  commuting `d` were not a scalar, every `d - λ` would be bijective with commuting inverse.
  For fixed `u ≠ 0`, operators of `B` that agree with `d` and with `(d - λ)⁻¹` at `u` would
  give a bounded operator with empty spectrum on the closure of `{e u | e commutes with B}`,
  which contradicts `spectrum.nonempty`.
* `ξ` is separating and tracial for `N` (`hsep`, `hnorm`).

No vector of `V` is ever written as `x ξ` with `x ∈ N`, and no element of `V` is assumed to
be a bounded vector. The proof picks `v ≠ 0` in `V` and takes the orthogonal projection `q`
onto `Q = {h | ∀ c ∈ B, c v = 0 → c h = 0}`. `Q` is closed and invariant under the
translations and their adjoints, because each `c ∈ B` commutes with them. So `q ∈ N`,
`q v = v`, and `q ξ ≠ 0` by `hsep`. For a linearly independent family `v₁, …, vₙ` in `V`,
the Jacobson density theorem with the bounded Schur lemma gives `a i ∈ B` with
`a i (v j) = δ_{ij} v`. Transitivity gives `c j ∈ B` with `c j v = v j`. Each
`a i * c j - δ_{ij}` lies in `B` (the identity of `H` is in `B`) and kills `v`, so
`a i * c j * q = δ_{ij} q`. Hence `p = Σ_j c j * q * q * a j` is an idempotent of `N` with
`⟪ξ, p ξ⟫ = n ‖q ξ‖²`. For the orthogonal projection `r` onto `ker (1 - p)` the trace
property gives `⟪ξ, p ξ⟫ = ⟪ξ, r ξ⟫ = ‖r ξ‖² ≤ ‖ξ‖²`. So `n ≤ ‖ξ‖² / ‖q ξ‖²`, and `V` is
finite dimensional.

## Lean proof

* `centerMul`: closure under products and inverses uses that central elements commute with
  everything. `centerChar` is multiplicative because `centerPart (j j')` and
  `centerPart j * centerPart j'` differ by a central element of `K`, on which `χ` is `1`
  (`char_centerPart`).
* `exists_compact_le_ker`: the kernel of `χ` is open in `Z(G)`, so it is `t ∩ Z(G)` for an
  open `t ∋ 1` (`isOpen_induced_iff`). Van Dantzig's theorem gives a compact open subgroup
  inside `t ∩ K₀`.
* `finite_quotient_heckeSub`: `heckeSub K g` is open in the compact group `K`
  (`Subgroup.quotient_finite_of_isOpen`).
* `tsum_coefficient_ne_top`: `Φ g = ‖ℓ(π(g) y)‖ₑ²` is right `J`-invariant
  (`coefficient_mul`, `‖ψ j‖ = 1`). `CentralCoset.lintegral_out_eq_mul_tsum` gives
  `∫⁻ Φ (q.out) dμ = μ(image of J) * ∑' α, Φ α.out`. The left side is finite by `hL2`, and
  the measure is nonzero, so the sum is finite.
* `coeffMap`: `Langlands.Analysis.memℓp_two_of_tsum_enorm_ne_top` with
  `tsum_coefficient_ne_top`; linearity is pointwise.
* `lift_coeffMap`: `TwistedCoset.lift_restrict` with `coefficient_mul`.
* `coeffMap_injective`: if `coeffMap y = 0`, then `ℓ(π(g) y) = 0` for all `g` by
  `lift_coeffMap`. If `y ≠ 0`, the orbit of `y` spans `V`, so `ℓ = 0`.
* `hecke_coeffMap`: `heckeSub K g` fixes `π(g) y`. So `Plancherel.averageMap_eq_finiteMean_cosets`
  writes the `K`-average of `π(g) y` as the mean of `π(q.out) π(g) y` over
  `q ∈ K ⧸ heckeSub K g`. Applying `ℓ ∘ π(α.out)` gives `heckeFun g (coeffMap y) α.out`,
  by `lift_coeffMap`.
* `finiteDimensional_fixedVectors`: as described in the previous section. The hypotheses
  of `TwistedCoset.tsum_enorm_heckeFun_le` (the bound `hb`) come from `norm_centerChar`,
  `le_centerMul`, `centerChar_of_mem`, `center_le_centerMul`, `isOpen_centerMul`, the
  definition of `centerMul` and `centralImage_centerMul_ne_top`. The image of `coeffMap` is
  finite dimensional, and `coeffMap` is injective, so `LinearEquiv.ofInjective` transfers
  finite dimensionality.
* `isAdmissible_of_memLp`: a nonzero coefficient forces `x ≠ 0` and `ℓ ≠ 0`.
  `memLp_coefficientNorm_of_irreducible` gives `hall`. For an open subgroup `K₀`, choose
  `K ⊆ K₀` by `exists_compact_le_ker` (`c.isOpen_ker`). The `K₀`-fixed vectors lie in the
  finite-dimensional space of `K`-fixed vectors.
* `singleCoefficientSquareIntegrability`: `isAdmissible_of_memLp` makes `π` admissible.
  `squareIntegrableCoefficientCriterion` then gives a unitary central character `c'` for
  which all coefficients are square-integrable. `c.coefficientNorm_eq c'` identifies the
  two coefficient norms.

## Files

This file imports, besides the Library, the modules
`Langlands/Analysis/BoundedSchur.lean`, `Langlands/Analysis/TracialFiniteness.lean`,
`Langlands/Analysis/FiberLIntegral.lean`,
`Langlands/Representation/MatrixCoefficient/CentralCosetSum.lean`,
`Langlands/Representation/MatrixCoefficient/TwistedCosetSpace.lean` and
`Langlands/Representation/MatrixCoefficient/HeckeOperator.lean`, each with its own Markdown.
The Library imports are `SquareIntegrableCoefficientCriterionProof`,
`Compact.ProjectionProof` (`Compact.averageMap`) and
`Plancherel.CompactIntertwiningCompression` (`averageMap_eq_finiteMean_cosets`).
