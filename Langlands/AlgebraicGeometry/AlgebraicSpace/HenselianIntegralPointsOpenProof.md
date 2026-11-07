# Integral points over a henselian valuation ring form an open set

Author: Worker 105.

Proof of `Langlands.AlgebraicGeometry.AlgebraicSpace.HenselianIntegralPointsOpenStatement.{u}`,
the openness part of Corollary 5.7 of Brian Conrad, *Weil and Grothendieck approaches to
adelic points* (December 31, 2011), printed p.16. The entry theorem is
`henselianIntegralPointsOpen`.

The target: let `K : Type u` be a nontrivially normed field whose closed unit ball is a
subring `O` (`∀ x, x ∈ O ↔ ‖x‖ ≤ 1`), assume `HenselianLocalRing O`, and let `X` be an
algebraic space over `Spec O` that is quasi-separated (`IsQuasiSeparated X`) and locally of
finite type over the base (`LocallyOfFiniteTypeOverBase X`). Let `X_K` be the base change
`baseChange (Spec.algebraMap O K) X`. Consider the map
`ι : X(O) → X_K(K)`, `x ↦ (baseChangeRingPointsEquiv O K K X).symm
(RingPoints.changeRing (Algebra.ofId O K) x)`. Then the range of `ι` is open for
`etaleChartTopology K X_K`.

The proof does not use the quasi-separatedness hypothesis.

## Route

The Lean proof follows Conrad's argument on printed p.16:

1. every `O`-point of `X` comes from an `O`-point of an affine étale chart `U → X`. Conrad
   chooses `U` with a rational point in the fibre over the closed point and uses that `O`
   is henselian;
2. `U(O)` is open in `U_K(K)`;
3. the chart map `U_K(K) → X_K(K)` is open.

Conrad takes step 3 from the construction of the topology. Here it is proved from the
henselian openness of smooth maps on rational points, which the Library proves for affine
schemes. Step 1 needs the lifting of residue-field points to étale charts. For a field
base this is the Library's `RationalPointEtaleLiftProof`. The relative version over
`Spec O` is proved in `FieldPointEtaleLift`, also by Worker 105.

## Declarations

Namespace `Langlands.AlgebraicGeometry.PointTopology.HenselianUnitBall`:

- `isUltrametricDist`: if the closed unit ball of `K` is a subring, then `K` is
  ultrametric. For `‖x‖ ≤ 1`, `x + 1` lies in the ball. Mathlib's
  `IsUltrametricDist.isUltrametricDist_of_forall_norm_add_one_of_norm_le_one` then applies.
- `eq_valuationSubring`: for ultrametric `K`, the subring `O` equals
  `(NormedField.valuation (K := K)).valuationSubring.toSubring`, since both are
  `{x | ‖x‖ ≤ 1}`.
- `henselianLocalRing_valuationSubring`: `HenselianLocalRing O` gives
  `HenselianLocalRing (NormedField.valuation (K := K)).valuationSubring`, by substituting
  the equality above.
- `isOpenMap_smoothSchemePointMap` (for `K` with `IsUltrametricDist K` and a henselian norm
  valuation ring): a smooth morphism `f : X ⟶ Y` of schemes over `Spec K` induces an open
  map `X(K) → Y(K)` for `schemePointTopology`. The proof copies the Library's
  complete-field version `PointTopology.isOpenMap_smoothSchemePointMap`, with the
  henselian affine lemma `HenselianSmoothOpen.isOpenMap_affineSmoothPointMap` in place of
  the complete-field one. It restricts `f` to affine opens `D ⊆ f⁻¹(V)` around a point,
  and pushes forward along the open affine chart embeddings
  (`isOpenEmbedding_schemeAffineChart`).
- `isOpen_range_changeRing`: for ultrametric `K` and `U` over `Spec O` affine and locally
  of finite type, the range of `RingPoint.changeRing (Algebra.ofId O K) : U(O) → U(K)` is
  open for `schemePointTopology O U K`. By `schemePointTopology_eq_affine` the topology is
  induced from `affineSchemePointEquiv O U K` into `AlgPoint O A K`, `A` the coordinate
  ring. `A` is a finitely generated `O`-algebra (`affineCoordinate_finiteType`); choose
  generators `s`. The range is the preimage of
  `⋂ a ∈ s, {φ | ‖φ a‖ ≤ 1}`. This set is open, because ultrametric closed balls are open
  (`IsUltrametricDist.isOpen_closedBall`) and evaluation is continuous. A point `φ` with
  `φ(s) ⊆ O` has all values in `O` (induction over `Algebra.adjoin`), so it corestricts
  to an `O`-algebra map `A → O`. The comparison uses `affineSchemePointEquiv_changeRing`.

The proof reuses the following theorem in
`Langlands.AlgebraicGeometry.AlgebraicSpace`, imported from the published
`HenselianCompletionPointEmbeddingProof`:

- `isOpenMap_schemePointsMap_of_etaleOpen`: for a nontrivially normed field `K`, assume
  étale maps between schemes locally of finite type over `K` are open on rational points.
  Then every étale `a : h_U ⟶ X.presheaf` with `U` locally of finite type gives an open
  map `schemePointsMap a : U(K) → X(K)` for `etaleChartTopology K X`. For each chart `d`,
  the preimage of an image is the image of a preimage through the pair pullback
  `U ×_X d` (`preimage_image_schemePointsMap`), whose second projection is étale.

The following helpers are in
`Langlands.AlgebraicGeometry.AlgebraicSpace.HenselianIntegralPointsOpen`:

- `locallyOfFiniteType_of_isEtale`: over any base scheme `S`, the source of an étale map
  `h_U ⟶ X.presheaf` to a space locally of finite type over `S` is locally of finite type
  over `S`. This is the Library's `AlgebraicSpace.locallyOfFiniteType_of_isEtale` with the
  base generalized from `Spec K`; the proof is the same (descent along the étale
  surjective atlas).
- `exists_integral_chart_point`: let `O` be a henselian local ring, `X` an algebraic space
  over `Spec O` and `x ∈ X(O)`. Then there are `U` over `Spec O` with `U.left` affine, a
  morphism `f : U → X` with `hom f` étale, and `u ∈ U(O)` with
  `RingPoints.map f ((schemeRingPointsEquiv O U O).symm u) = x`.
- `baseChangeRingPointsEquiv_schemePointsMap`: for `f : U → X` over `Spec O` and a
  `K`-point `p` of `U_K = ringBaseChange O K U`, the base-changed chart
  `restrictAtlas (Spec.algebraMap O K) (hom f)` sends `p` to the point of `X_K` that
  `baseChangeRingPointsEquiv` identifies with
  `RingPoints.map f ((schemeRingPointsEquiv O U K).symm ((ringPointBaseChangeEquiv O K K U).symm p))`.
  The proof is naturality of `mapSections`.

Namespace `Langlands.AlgebraicGeometry.AlgebraicSpace`:

- `henselianIntegralPointsOpen : HenselianIntegralPointsOpenStatement.{u}`.

## Proof of `exists_integral_chart_point`

Let `κ = IsLocalRing.ResidueField O`, so `O → κ` is surjective.

1. `FieldPointEtaleLift.exists_affine_etale_point`, applied to the residue point
   `RingPoints.changeRing (Algebra.ofId O κ) x`, gives an affine `U`, an étale
   `f : U → X` and `ū ∈ U(κ)` mapping to it.
2. Let `P = U ×_X Spec O` be the represented pullback of `a = hom f` along
   `x̂ = uliftYonedaEquiv.symm x`, with projections `p : P → Spec O` (étale) and
   `q : P → U`. Through `uliftYonedaEquiv` and `uliftYonedaEquiv_naturality`, the equation
   of step 1 says `h(ū) ≫ a = h(Spec κ → Spec O) ≫ x̂`. So `ū` and `Spec κ → Spec O`
   lift to `b : Spec κ → P` with `b ≫ p = Spec κ → Spec O`.
3. `CommutativeAlgebra.HenselianSections.exists_section_of_smooth_of_surjective` (Library;
   étale implies smooth) gives a section `σ` of `p`.
4. Take `u = σ ≫ q`. Then `h(u) ≫ a = h(σ ≫ p) ≫ x̂ = x̂` by the pullback square, so `u`
   maps to `x`.

## Proof of `henselianIntegralPointsOpen`

1. From the unit-ball hypothesis, `K` is ultrametric and its norm valuation ring is
   henselian (`HenselianUnitBall`).
2. Fix `x ∈ X(O)`. `exists_integral_chart_point` gives an affine `U`, an étale `f` and
   `u ∈ U(O)` over `x`. `U` is locally of finite type over `O`
   (`locallyOfFiniteType_of_isEtale`), hence so is `U_K` over `K`, and the base-changed
   chart `a_K = restrictAtlas (Spec.algebraMap O K) (hom f) : h_{U_K} ⟶ X_K.presheaf` is
   étale (`relative_restrictAtlas`).
3. Let `S₀ ⊆ U(K)` be the range of `U(O) → U(K)`. It is open (`isOpen_range_changeRing`).
   `ringPointBaseChangeEquiv O K K U : U(K) ≃ U_K(K)` is a homeomorphism for the scheme
   point topologies (`schemeBaseChangeTopology_proof`).
4. `N = schemePointsMap a_K '' (ringPointBaseChangeEquiv O K K U '' S₀)` is open in
   `X_K(K)`, by `isOpenMap_schemePointsMap_of_etaleOpen` with the henselian
   `isOpenMap_smoothSchemePointMap`.
5. For `v ∈ U(O)`, the image of `v` in `N` equals `ι (RingPoints.map f v)`
   (`hcompat`; by `baseChangeRingPointsEquiv_schemePointsMap`,
   `RingPoints.changeRing_map` and `schemeRingPointsEquiv_changeRing`). Hence `N` lies in
   the range of `ι` and contains `ι x`. So the range of `ι` is a neighbourhood of each of
   its points.

The proof uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

## Sources

- Conrad, registered source `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
  `fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`, Corollary 5.7 and
  the first paragraph of its proof, printed p.16.
