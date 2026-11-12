# Pro-`p` levels

Author: Worker 19.

Harris (1999) chooses an open normal pro-`p` subgroup `H_p` of a maximal
compact subgroup `C_p`, contained in a given level `K_p`. This module proves
that such subgroups exist in a general setting. It builds them in any
topological group that is totally disconnected and has an open subgroup on
which `p`-power iteration converges to `1`. It then gives such subgroups in
the unit group of a finite-dimensional algebra over a complete ultrametric
field. The application to unitary similitude groups is in
`Langlands.Shimura.Unitary.HarrisProPLevels`.

## Source

Harris (1999), Section 4, printed p. 310 (PDF p. 12): "To continue, we fix a
compact open subgroup `K_p ⊂ GJ_p` contained in a fixed maximal compact
subgroup `C_p`. [...] Let `H_p` be an open normal pro-`p` subgroup of `C_p`
contained in `K_p`, and let `H(m) = K^{ℓ,p} × K_ℓ(m) × H_p`; when `m = 1` we
just write `H`."

Harris takes such an `H_p` as given. The construction here is the standard
one: take the normal core of `K_p ∩ P` in `C_p`, for an open subgroup `P` of
principal units.

## Declarations

All declarations are in namespace `Langlands.Shimura`.

### Topological `p`-torsion and pro-`p` subgroups

Let `G` be a topological group.

- `IsTopologicallyPTorsion p H`, for a subgroup `H` of `G`: for every `h ∈ H`,
  `h ^ (p ^ k) → 1` as `k → ∞`.
- `IsTopologicallyPTorsion.mono`: the property passes to smaller subgroups.
- `IsTopologicallyPTorsion.comap`: it pulls back along an inducing
  homomorphism.
- `IsTopologicallyPTorsion.prod`: `H × H'` has it when `H` and `H'` do.
- `IsTopologicallyPTorsion.isPGroup_quotient`: the quotient of such an `H` by
  an open normal subgroup is a `p`-group. For `h ∈ H`, the powers
  `h ^ (p ^ k)` eventually lie in the open subgroup.
- `IsTopologicallyPTorsion.isProPSubgroup`: such an `H`, compact and totally
  disconnected in the subspace topology, is pro-`p` in the sense of the
  published `Langlands.Cohomology.IsProPSubgroup` (`p` prime, `H` compact and
  totally disconnected, every quotient by an open normal subgroup a
  `p`-group).

### Normal cores in a compact open level

Let `G` be a topological group, `C` a published `CompactOpenLevel G` and `U`
an open subgroup of `G`.

- `CompactOpenLevel.normalCoreIn C U hU` is the compact open level obtained as
  the image in `G` of the normal core in `C` of `U ∩ C`. The normal core is
  the intersection of the `C`-conjugates. It is closed because `U ∩ C` is
  open, hence closed, in `C`. It is open because `U ∩ C` has finite index in
  the compact group `C`.
- `mem_normalCoreIn` describes membership.
- `normalCoreIn_le` and `normalCoreIn_le_self` show that it lies in `U` and in
  `C`.
- `normalCoreIn_subgroupOf` and the instance `normalCoreIn_normal` show that,
  as a subgroup of `C`, it is the normal core, and so is normal in `C`.

### Harris's `H_p`

- `NormalProPLevel p C K`, for a compact open level `C` and a subgroup `K` of
  `G`, is a structure. Its fields are a compact open level `level` (Harris's
  `H_p`) with proofs that:
  - `level ⊆ K`;
  - `level ⊆ C`;
  - `level` is normal in `C`;
  - `level` is pro-`p` (`Cohomology.IsProPSubgroup`).

  The structure does not require `K ⊆ C`; Harris's setting `K_p ⊆ C_p` is
  the special case.
- `NormalProPLevel.ofNormalCore hp C hK hP hPp`: let `G` be totally
  disconnected, `p` prime, `K` and `P` open subgroups, and `P` topologically
  `p`-torsion. Then the normal core in `C` of `K ∩ P ∩ C` is a
  `NormalProPLevel p C K`.
- `NormalProPLevel.nonempty` states the existence.

### Principal units in ultrametric normed rings

Let `S` be a normed ring whose norm is ultrametric, with `‖1‖ ≤ 1`.

- `PrincipalUnits.norm_le_one`, `norm_pow_le_one`, `norm_geom_sum_le_one`,
  `norm_pow_sub_one_le`: if `‖x - 1‖ ≤ 1`, then `‖x‖`, `‖x ^ n‖` and
  `‖∑_{i<n} x ^ i‖` are at most `1`, and `‖x ^ n - 1‖ ≤ ‖x - 1‖`.
- `PrincipalUnits.norm_pow_sub_one_le_max_mul`: the estimate
  `‖x ^ p - 1‖ ≤ max ‖p‖ ‖x - 1‖ * ‖x - 1‖`. It follows from
  `x ^ p - 1 = (p + ∑_{i<p} (x ^ i - 1)) (x - 1)`.
- `PrincipalUnits.norm_pow_pow_sub_one_le`: if `‖x - 1‖ ≤ r ≤ 1`, then
  `‖x ^ (p ^ k) - 1‖ ≤ (max ‖p‖ r) ^ k ‖x - 1‖`.
- `PrincipalUnits.tendsto_pow_pow`: if `‖p‖ < 1` and `‖x - 1‖ < 1`, then
  `x ^ (p ^ k) → 1`.
- `principalUnits h1 r hr0 hr`, for `0 ≤ r < 1`, is the subgroup
  `{u ∈ Sˣ | ‖u - 1‖ ≤ r}` (`mem_principalUnits`). It is closed under
  products by `ab - 1 = (a - 1)(b - 1) + (a - 1) + (b - 1)`. It is closed
  under inverses because `‖u⁻¹‖ ≤ 1` and `u⁻¹ - 1 = -u⁻¹ (u - 1)`.
- `isOpen_principalUnits`: for `0 < r`, it is open, because closed balls of
  positive radius are open in an ultrametric space.
- `isTopologicallyPTorsion_principalUnits`: if `‖p‖ < 1`, it is
  topologically `p`-torsion. The units carry the topology of `Sˣ ⊆ S × Sᵐᵒᵖ`,
  so the proof checks convergence of both `u ^ (p ^ k)` and `u⁻¹ ^ (p ^ k)`.

### Finite-dimensional algebras over ultrametric fields

Let `𝕜` be a complete nontrivially normed field and `R` a finite-dimensional
`𝕜`-algebra.

- `norm_one_continuousLinearMap_le`, `norm_natCast_continuousLinearMap_le`:
  in `E →L[𝕜] E` with the operator norm, `‖1‖ ≤ 1` and `‖n‖ ≤ ‖(n : 𝕜)‖`.
- `isUltrametricDist_continuousLinearMap`: if the norm of `E` is ultrametric,
  so is the operator norm on `E →L[𝕜] E`.
- `RegularCoordinates 𝕜 R` is `𝕜ⁿ` with the sup norm, `n = dim_𝕜 R`.
  `RegularEndomorphisms 𝕜 R` is its algebra of continuous endomorphisms with
  the operator norm. The operator norm is ultrametric when the norm of `𝕜`
  is (instance).
- `regularRepresentation 𝕜 R : R →ₐ[𝕜] RegularEndomorphisms 𝕜 R` is left
  multiplication written in the coordinates of `Module.finBasis 𝕜 R`
  (`regularRepresentation_apply`). It is injective
  (`regularRepresentation_injective`).
- `regularPrincipalUnits 𝕜 R r hr0 hr` is the subgroup of units `u` of `R`
  with `‖ρ(u) - 1‖ ≤ r` (`mem_regularPrincipalUnits`). It is the inverse
  image of `principalUnits` under `ρ`.

Give `R` its module topology (`IsModuleTopology 𝕜 R`).

- `continuous_regularRepresentation`, `isInducing_regularRepresentation`: `ρ`
  is continuous and a topological embedding. `ρ` is an injective linear map
  from a finite-dimensional space, so it is a closed embedding.
- `t2Space_of_isModuleTopology`: `R` is Hausdorff.

Assume moreover that the norm of `𝕜` is ultrametric.

- `totallyDisconnectedSpace_units`: `Rˣ` is totally disconnected. It injects
  continuously into the ultrametric, hence totally separated, space
  `RegularEndomorphisms 𝕜 R`
  (`totallyDisconnectedSpace_of_continuous_injective`).
- `isOpen_regularPrincipalUnits`: for `0 < r`, `regularPrincipalUnits` is
  open.
- `isTopologicallyPTorsion_regularPrincipalUnits`: if `‖(p : 𝕜)‖ < 1`, it is
  topologically `p`-torsion. The proof pulls the property back along the
  embedding `Rˣ → (RegularEndomorphisms 𝕜 R)ˣ` (`isInducing_units_map`: the
  map on units of an inducing monoid homomorphism is inducing).

## Scope

- The module gives existence by one explicit construction: the normal core of
  `K ∩ P` in `C`. Harris only requires some open normal pro-`p` subgroup of
  `C_p` contained in `K_p`. A statement about Harris's `H_p` should be
  stated for an arbitrary `NormalProPLevel`, not for this construction.
- The radius `1/2` used later in `HarrisProPLevels` is one choice. Any radius
  in `(0, 1)` gives an open topologically `p`-torsion subgroup.
- The unit group of a finite-dimensional algebra is treated through its left
  regular representation. No integral structure (orders, lattices) is used.
- `t2Space_of_isModuleTopology` generalizes the published
  `Langlands.Shimura.LocalDivision.t2Space_of_isModuleTopology` from division
  algebras to all finite-dimensional algebras. The names differ by namespace.

## Provenance

The notion "open normal pro-`p` subgroup of `C_p` contained in `K_p`" is from
Harris (1999), Section 4, printed p. 310, read in the original. Harris takes
such a subgroup as given. The existence proof is a standard argument written
for this module. It combines the topologically `p`-torsion criterion, the
normal core in a compact group, and the principal-unit estimate
`‖x ^ p - 1‖ ≤ max ‖p‖ ‖x - 1‖ ‖x - 1‖` in an ultrametric normed ring.

Source ID and SHA-256 fingerprint:

- `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`:
  `525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Formal dependencies:

- the published `Langlands.Cohomology.DivisibleSystem.ProPInvariants`
  (`Cohomology.IsProPSubgroup`);
- the published `Langlands.Shimura.Levels` (`CompactOpenLevel`);
- Mathlib `5ed2965256430c3649e86755f9576b54eca72435` under Lean 4.34.0.

The Mathlib results used include:

- `Subgroup.normalCore` with `Subgroup.normalCore_isClosed` and
  `Subgroup.isOpen_of_isClosed_of_finiteIndex`;
- `Subgroup.quotient_finite_of_isOpen`;
- `IsUltrametricDist.isOpen_closedBall` and
  `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg`;
- `geom_sum_mul`;
- `IsModuleTopology.continuous_of_linearMap` and
  `LinearMap.isClosedEmbedding_of_injective`;
- `Module.End.toContinuousLinearMap`;
- `Units.isInducing_embedProduct`;
- `isTotallyDisconnected_of_image`.
