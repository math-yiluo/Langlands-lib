# Integral points over a locally compact henselian valuation ring are quasi-compact

Author: Worker 105.

Proof of `Langlands.AlgebraicGeometry.AlgebraicSpace.HenselianIntegralPointsCompactStatement.{u}`,
the quasi-compactness part of Corollary 5.7 of Brian Conrad, *Weil and Grothendieck
approaches to adelic points* (December 31, 2011), printed pp.16–17. The entry theorem is
`henselianIntegralPointsCompact`.

The target: let `K : Type u` be a nontrivially normed field whose closed unit ball is a
subring `O` (`∀ x, x ∈ O ↔ ‖x‖ ≤ 1`). Assume `HenselianLocalRing O` and
`LocallyCompactSpace K`, and let `X` be an algebraic space over `Spec O` that is
quasi-separated (`IsQuasiSeparated X`) and of finite type (`FiniteTypeOverRing O X`). Then
the image of
`ι : X(O) → X_K(K)`, `x ↦ (baseChangeRingPointsEquiv O K K X).symm
(RingPoints.changeRing (Algebra.ofId O K) x)`, is quasi-compact for
`etaleChartTopology K X_K`, where `X_K = baseChange (Spec.algebraMap O K) X`.

## Route

The Lean proof follows Conrad's argument on printed p.17. The residue field `κ` of `O` is
finite, so the special fibre has finitely many rational points. Charts covering the
`O`-points over each of them can be chosen of finite type. Their `O`-points are compact, and
the image of `X(O)` is a finite union of their images. Conrad's finite stratification of `X`
by schemes is replaced by the module `FiniteFieldPoints`.

## Declarations

Namespace `Langlands.AlgebraicGeometry.PointTopology.HenselianUnitBall` (for `K` and `O` as
above):

- `isUnit_iff_norm_eq_one`: `y ∈ O` is a unit of `O` exactly when `‖y‖ = 1`.
- `mem_maximalIdeal_iff`: `y ∈ O` lies in the maximal ideal exactly when `‖y‖ < 1`.
- `compactSpace`: if `K` is locally compact, `O` is a compact space. `K` is proper
  (`ProperSpace.of_locallyCompactSpace`), and `O` is the closed ball of radius `1`.
- `finite_residueField`: if `K` is locally compact, `IsLocalRing.ResidueField O` is finite.
  Give the residue field the discrete topology. The residue map is continuous, since the
  fibre over the class of `a` is `{y : ‖y - a‖ < 1}`, which is open. So the residue field is a
  compact discrete space (`finite_of_compact_of_discrete`).
- `isCompact_range_changeRing`: if `K` is locally compact and `U` over `Spec O` is affine and
  locally of finite type, the range of `RingPoint.changeRing (Algebra.ofId O K) : U(O) → U(K)`
  is compact for `schemePointTopology O U K`. `U(O)` is compact by the Library's
  `affineSchemeCompactness_proof` (compact Hausdorff value ring `O`). The coefficient change is
  continuous by `affineSchemeCoefficientContinuity_proof`, and the topologies agree with the
  affine ones (`schemePointTopology_eq_affine`).

Namespace `Langlands.AlgebraicGeometry.AlgebraicSpace.HenselianIntegralPointsCompact`:

- `exists_point_of_residue_point`: let `O` be a henselian local ring, `f : U → X` a morphism
  from a scheme with `hom f` étale, and `x ∈ X(O)`. Suppose `ū` is a residue-field point of
  `U` whose image is the residue point of `x`. Then `x` is the image of an `O`-point of `U`.
  The proof is that of `HenselianIntegralPointsOpen.exists_integral_chart_point` (module
  `HenselianIntegralPointsOpenProof`), with the chart and residue point given rather than
  constructed. The `κ`-point given by `ū` and `x` of the étale `O`-scheme `U ×_X Spec O`
  extends to a section (`CommutativeAlgebra.HenselianSections.exists_section_of_smooth_of_surjective`).

Namespace `Langlands.AlgebraicGeometry.AlgebraicSpace`:

- `henselianIntegralPointsCompact : HenselianIntegralPointsCompactStatement.{u}`.

## Proof of `henselianIntegralPointsCompact`

1. `K` is ultrametric (`HenselianUnitBall.isUltrametricDist`). The residue field `κ` is finite
   (`finite_residueField`), so `X(κ)` is finite (`FiniteFieldPoints.finite_ringPoints`). `X`
   is locally of finite type over the base, because its finite-type atlas is.
2. For every `x̄ ∈ X(κ)` choose, by `FieldPointEtaleLift.exists_affine_etale_point`, an affine
   `U_x̄`, an étale `f_x̄ : U_x̄ → X` and `ū_x̄ ∈ U_x̄(κ)` over `x̄`. `U_x̄` is locally of
   finite type over `O` (`HenselianIntegralPointsOpen.locallyOfFiniteType_of_isEtale`).
3. Let `N_x̄` be the image in `X_K(K)` of `U_x̄(O)` under
   `U_x̄(O) → U_x̄(K) ≃ (U_x̄)_K(K) → X_K(K)`. The last map is `schemePointsMap` of the
   base-changed chart `restrictAtlas (Spec.algebraMap O K) (hom f_x̄)`. As in the openness
   proof (`hcompat`, using `baseChangeRingPointsEquiv_schemePointsMap`), the image of
   `v ∈ U_x̄(O)` is `ι (f_x̄ v)`.
4. The range of `ι` is `⋃_x̄ N_x̄`. Each `N_x̄` lies in the range by step 3. Conversely, for
   `x ∈ X(O)` with residue point `x̄`, `exists_point_of_residue_point` gives
   `u ∈ U_x̄(O)` over `x`, so `ι x ∈ N_x̄`.
5. Each `N_x̄` is compact. The range of `U_x̄(O) → U_x̄(K)` is compact
   (`isCompact_range_changeRing`). Its image under the homeomorphism `ringPointBaseChangeEquiv O K K U_x̄`
   (`schemeBaseChangeTopology_proof`) is mapped by the chart map, which is continuous (`EtaleFiniteTypeChart.continuous_pointMap`): the base-changed chart is étale,
   locally of finite type and quasi-compact over `Spec K`, so it is an étale chart of finite
   type. Since `X(κ)` is finite, the union is compact (`isCompact_iUnion`).

The proof uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

## Sources

- Conrad, registered source `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
  `fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`, Corollary 5.7 and the
  last paragraph of its proof, printed pp.16–17.
