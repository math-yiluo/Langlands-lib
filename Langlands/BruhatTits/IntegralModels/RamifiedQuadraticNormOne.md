# Regression: the ramified quadratic norm-one torus

This module computes a ramified example for the norm-one models of
`Langlands.BruhatTits.IntegralModels.NormOneTorusDepthZero`.

Let `F` be a nonarchimedean local field in which `2` is a unit of `𝒪[F]`,
that is, of odd residue characteristic. Let `ϖ` be an irreducible element of
`𝒪[F]`, that is, a uniformizer. The module takes:

- `B = 𝒪[F][X] / (X ^ 2 - ϖ)`, which is finite free of rank `2` over `𝒪[F]`
  with basis `1, α`, where `α` is the class of `X`;
- `E = F[X] / (X ^ 2 - ϖ)`, a separable quadratic field extension of `F`,
  with `F ⊗[𝒪[F]] B ≃ₐ[F] E`.

Write `T = R¹_{E/F} G_m` for the norm-one torus over `F`. Its model
`R¹_{B/𝒪[F]} G_m` is smooth over `𝒪[F]` by the trace criterion
`normOne_smooth_of_hasTraceOne`, because `1 / 2` has trace one in `B`.

The module proves:

- the norm of `a + b α` is `a ^ 2 - ϖ b ^ 2`;
- the `𝓀[F]`-points of the special fibre are the elements `x + y α` of
  `𝓀[F][α] / (α ^ 2)` with `x ^ 2 = 1`. Their sign `x` takes exactly the
  values `1` and `-1` (here `2 ≠ 0` in `𝓀[F]`), so the points of sign `1`
  form a subgroup of index `2`;
- the component points, the integral points whose reduction has sign `1`,
  form a subgroup of index `2` in the integral points. They contain the
  congruence subgroup;
- every point of `T(F)` is integral: if `a ^ 2 - ϖ b ^ 2 = 1` in `F`, then
  `a` and `b` lie in `𝒪[F]`;
- hence the component points have index `2` in `T(F)`.

## Provenance

The module is derived. It is a regression example for the task objective
(Task 3557, section "Regression examples"): a computation over concrete
data whose value is compared with a value stated by Kaletha and Prasad. The
algebra is standard and proved here from Mathlib and the Library; no
external code is adapted.

The comparison values come from Kaletha–Prasad, *Bruhat–Tits Theory: A New
Approach* (2023). The registered original is
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
The authors' corrections of 1 November 2024 are
`kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`.

- Proposition 2.5.8 (printed p. 88 / PDF p. 119) defines `T(k)_1`, the
  maximal bounded subgroup of `T(k)`. Definition 2.5.13 (printed p. 90 /
  PDF p. 121) defines the Iwahori subgroup `T(k)_0`. The corrections do not
  amend these two items; in Section 2.5 they amend only 2.5(b), Remark 2.5.11
  and Remark 2.5.15.
- The corrections replace Remark 2.5.15 (Section 2.5, PDF pp. 24–25). The
  corrected remark treats the kernel `T` of the norm map
  `R_{ℓ/k} G_m → G_m` for a separable quadratic extension `ℓ / k`. It
  identifies `T(k)_0 = o_ℓ^× / o_k^× ⊂ ℓ^× / k^× = T(k)_1 = T(k)`. When
  `ℓ / k` is ramified, the inclusion has index `2`. When `ℓ / k` is tamely
  ramified, it also identifies `T(k)_0 = (1 + p_ℓ) ∩ ℓ^1`. The remark's proof
  uses a uniformizer of `ℓ` whose Galois conjugate is its negative; `α`
  is such a uniformizer here.

The comparison is as follows. Here `ℓ = E` and `k = F`. The extension is
ramified and, since the residue characteristic is odd, tamely ramified.
Every norm-one element is `a + b α` with `a, b ∈ 𝒪[F]`
(`integralPoints_eq_top`). Its sign is the residue of `a`. So the component
points are the norm-one elements of `1 + α 𝒪[F][α]`. Mathematically
`𝒪[F][α]` is the ring of integers of `E` (`X ^ 2 - ϖ` is Eisenstein) and
`α` generates its maximal ideal. Then the component points are
`(1 + p_E) ∩ E^1`, KP's description of `T(F)_0`. The Lean index `2`
(`index_componentPoints`) is KP's index `2`. `integralPoints_eq_top` matches
`T(F)_1 = T(F)`. Only the values are compared; see "Scope".

KP's objects are not used in the Lean statements. The Library's
`integralPoints` and `congruenceSubgroup` and the new `componentPoints` are
computed for the constructed data.

## Setting

The file imports:

- `Langlands.BruhatTits.IntegralModels.NormOneTraceSmoothness`, for
  `HasTraceOne`, `hasTraceOne_of_isUnit_finrank` and
  `normOne_smooth_of_hasTraceOne`. Through it, it also imports
  `NormOneTorusDepthZero`, for `normOneModel`, `normOneCoeffEquiv`,
  `residueSectionsEquiv`, `normOneCongrUnitsEquiv`,
  `normOneCongrIso_hom_points` and `normOne_isAnisotropic`;
- `Langlands.CommutativeAlgebra.FiniteSeparableLiftedPolynomialModel`, for
  `adjoinRootBaseChangeEquiv` (base change of `AdjoinRoot`);
- `Langlands.BruhatTits.IntegralModels.DepthZeroInduction`, for
  `henselianLocalRing_integer`;
- `Langlands.GroupScheme.IntegralModel.HenselianReduction`, for
  `IntegralModel.reduction_surjective` (reduction of a smooth model over a
  henselian ring is surjective);
- `Mathlib.FieldTheory.KummerPolynomial`, for `X_pow_sub_C_irreducible_of_prime`.

`F` is a field in universe `u` with `ValuativeRel F`. The declarations from
`smooth` on, and `nonempty_iff`, also assume `TopologicalSpace F` and
`IsNonarchimedeanLocalField F`; the few that do not need these assumptions
omit them. `𝒪[F]` is the valuation ring and `𝓀[F]` its residue field.

The file opens `CategoryTheory.MonObj` (scoped) for the group structure on
`rationalPoints`. It sets `backward.isDefEq.respectTransparency false`.

## Declarations

### The norm on a quadratic basis (namespace `Langlands.Algebra`)

For a commutative ring `R` and `d : R`:

- `sqrtBasis d` (definition, `[Nontrivial R]`): the basis `1, α` of
  `AdjoinRoot (X ^ 2 - C d)` over `R`, from Mathlib's power basis.
  `sqrtBasis_apply`, `sqrtBasis_zero` and `sqrtBasis_one` give its values.
- `root_sq`: `α ^ 2 = d` in `AdjoinRoot (X ^ 2 - C d)`.
- `exists_eq_algebraMap_add_mul`: for an `R`-algebra `S` with a basis `β`
  indexed by `Fin 2` with `β 0 = 1` and `β 1 = r`, every element of `S` is
  `a + b r` with `a, b ∈ R`.
- `norm_algebraMap_add_mul`: with such a basis and `r ^ 2 = d`,
  `Algebra.norm R (a + b r) = a ^ 2 - d * b ^ 2`. The proof computes the
  determinant of the multiplication matrix in the basis `β`.
- `norm_of_add_of_mul_root` (`[Nontrivial R]`): the same formula in
  `AdjoinRoot (X ^ 2 - C d)`.

### The ramified quadratic data (namespace `Langlands.BruhatTits.IntegralModels`)

- `RamifiedQuadraticData F` (structure): fields `uniformizer : 𝒪[F]`,
  `irreducible : Irreducible uniformizer` and
  `isUnit_two : IsUnit (2 : 𝒪[F])`. Every irreducible element is allowed,
  so for odd residue characteristic both ramified quadratic extensions
  `F(√ϖ)` and `F(√(ε ϖ))`, with `ε` a non-square unit, arise. The Lean
  file does not state or prove that these are all ramified quadratic
  extensions.
- `RamifiedQuadraticData.nonempty_iff`: such data exist if and only if `2`
  is a unit in `𝒪[F]` (Mathlib's `IsDiscreteValuationRing.exists_irreducible`
  supplies the uniformizer).

For `D : RamifiedQuadraticData F`, in namespace `RamifiedQuadraticData`:

- `D.polynomial = X ^ 2 - C ϖ`, `D.Carrier = AdjoinRoot D.polynomial`
  (the algebra `B`) and `D.GenericField` (the field `E`) are
  abbreviations. Instances: `Module.Finite` and `Module.Free` over `𝒪[F]`
  for `B`; `FiniteDimensional` and `Algebra.IsSeparable` over `F` for `E`;
  `Fact (Irreducible ...)`, which makes `E` a field.
- `finrank_carrier`: `B` has rank `2`. `hasTraceOne`: `HasTraceOne 𝒪[F] B`.
- `not_isSquare`: `y ^ 2 ≠ ϖ` for every `y : F`. A square root of `ϖ` is
  integral over `𝒪[F]`, which is integrally closed, so it is some
  `z ∈ 𝒪[F]` with `z * z = ϖ`. Since `ϖ` is irreducible, `z` is a unit, and
  then so is `ϖ`, a contradiction.
- `polynomial_map_generic`, `irreducible_generic`: over `F` the polynomial
  is `X ^ 2 - ϖ` and is irreducible (Mathlib's
  `X_pow_sub_C_irreducible_of_prime`). `two_ne_zero_generic`,
  `uniformizer_ne_zero_generic` give the separability hypotheses.
- `genericEquiv : F ⊗[𝒪[F]] B ≃ₐ[F] E` (abbreviation), the published
  `adjoinRootBaseChangeEquiv`.
- `isAnisotropic`: `T` is anisotropic (published `normOne_isAnisotropic`).
- `smooth`: `Smooth (normOne (CommRingCat.of 𝒪[F]) D.Carrier).X.hom`, by the
  trace criterion.
- `model` (abbreviation): the published `normOneModel` for these data, a
  `LocalFieldIntegralModel F T`. `model_isSmooth`: it is smooth.

#### The special fibre

- `residue_uniformizer`: `ϖ` reduces to `0`. `two_ne_zero_residue`:
  `2 ≠ 0` in `𝓀[F]`.
- `residueRootZero` (definition): the `𝒪[F]`-algebra map `B → 𝓀[F]` with
  `α ↦ 0`. `specialFibreEval` (definition): the induced
  `𝓀[F]`-algebra map `𝓀[F] ⊗ B → 𝓀[F]`.
- `norm_eq_specialFibreEval_sq`: the norm of `z ∈ 𝓀[F] ⊗ B` is the square
  of `specialFibreEval z`, by `norm_algebraMap_add_mul` with `d = 0`.
- `specialFibrePointsEquiv` (definition): the `𝓀[F]`-points of the special
  fibre are, as a group, the kernel of the published `tensorNormUnits` on
  `(B ⊗ 𝓀[F])ˣ`. It composes the published `baseChangePointsEquiv`,
  `normOnePointsEquiv` and `normOneCoeffEquiv` with `residueSectionsEquiv`.
- `unitsEval` (definition): `(B ⊗ 𝓀[F])ˣ → 𝓀[F]ˣ`, `x + y α ↦ x`.
  `unitsEval_sq`: its square is the norm. `unitsEval_neg_one`,
  `neg_one_mem_ker`.
- `specialFibreSign` (definition): the homomorphism from the special-fibre
  points to `𝓀[F]ˣ` given by `unitsEval`. `specialFibreSign_sq`: its values
  square to `1`. `exists_specialFibreSign_eq_neg_one`: `-1` is a value.
  `one_ne_neg_one_units`: `1 ≠ -1` in `𝓀[F]ˣ`.
- `range_specialFibreSign`: the range is `{1, -1}`.
- `index_ker_specialFibreSign`: the kernel has index `2`.

#### Integral points

- `integralSign` (definition): `specialFibreSign` composed with the
  reduction map of the model.
- `range_integralSign`: it has the same range as `specialFibreSign`, since
  reduction is surjective (published `IntegralModel.reduction_surjective`,
  with `henselianLocalRing_integer` and smoothness).
- `componentPoints` (definition): the image in `T(F)` under the integral-point
  map of the kernel of `integralSign`. This is the module's main definition.
- `componentPoints_le_integralPoints`.
- `congruenceSubgroup_le_componentPoints`: the congruence subgroup (images
  of sections that reduce to `1`) lies in `componentPoints`.
- `relIndex_componentPoints`: `componentPoints` has relative index `2` in
  `D.model.integralPoints`. The integral-point map is injective, so this is
  the index of the kernel of `integralSign`.

#### Every point is integral

- `exists_integer_right_of_sq_sub`: if `a ^ 2 - ϖ b ^ 2 = 1` in `F`, then
  `b ∈ 𝒪[F]`. Otherwise `c = b⁻¹` is a non-unit of `𝒪[F]`, so `c = ϖ c'`.
  Then `a / b` is a root of `X ^ 2 - (c ^ 2 + ϖ)`, so it is some `t ∈ 𝒪[F]`
  with `t ^ 2 = ϖ (ϖ c' ^ 2 + 1)`. Hence `ϖ` divides `t`, and cancelling
  `ϖ` makes `ϖ` a unit, a contradiction.
- `exists_integer_of_sq_sub`: then `a ∈ 𝒪[F]` as well (a root of
  `X ^ 2 - (1 + ϖ b ^ 2)`), and the equation holds in `𝒪[F]`.
- `mul_conj`: `(a + b α) (a - b α) = a ^ 2 - ϖ b ^ 2` in `B`.
- `exists_unit_of_normOne`: for an `𝒪[F]`-algebra `S'` with
  `S' ≃ₐ[𝒪[F]] F`, every unit of `B ⊗ S'` of norm one is `c ⊗ 1` for a
  unit `c` of `B` of norm one.
- `genericSectionsEquiv` (definition): the global sections of `Spec F`,
  as an `𝒪[F]`-algebra, are `F`.
- `genericTensorEquiv` (definition): the published `normOneTensorEquiv` for
  base change from `𝒪[F]` to `F`, evaluated on the global sections of
  `Spec F`. Its instance arguments are written out. The published
  `normOneAlgebraBaseChangeIso_hom_points` is stated over a general
  `A : CommRingCat`. At `A = CommRingCat.of 𝒪[F]` it carries `CommRingCat`'s
  own ring instance, while terms written over `𝒪[F]` carry the subring
  instance. The two are equal, but checking this by unfolding timed out. The
  named definition uses the `CommRingCat` instance, so that the published
  lemma applies without unfolding.
- `integralPointMap_points`: on norm-one units, the integral-point map is
  restriction to the generic point, then `genericTensorEquiv`, then
  transport along `genericEquiv`. It combines the published
  `normOneCongrIso_hom_points`, `normOneAlgebraBaseChangeIso_hom_points`,
  `baseChangePointsEquiv_baseChangeSectionHom` and
  `normOnePointsEquiv_naturality`.
- `genericNormOneEquiv` (definition): `genericTensorEquiv` followed by
  the transport along `genericEquiv`; `genericNormOneEquiv_apply`.
- `constantNormOne` (definition): a norm-one unit `c` of `B` gives the
  norm-one unit `c ⊗ 1` of `B ⊗ S`, by the published `tensorNorm_naturality`.
  `constantNormOne_val`; `normOneUnitsRestrict_constantNormOne`: it is
  unchanged by restriction along test morphisms.
- `integralPoints_eq_top`: `D.model.integralPoints = ⊤`. A point of `T(F)`
  corresponds under `genericNormOneEquiv` to a norm-one unit of
  `B ⊗ Γ(Spec F)`, which is `c ⊗ 1` by `exists_unit_of_normOne`. The
  integral section given by `c` maps to the point.
- `index_componentPoints`: `componentPoints` has index `2` in all of
  `T(F)`.

## Scope

- `B` is not shown to be the ring of integers of `E`, and `E / F` is not
  shown to be ramified in any Library sense. The model is not identified
  with the Néron model or a Bruhat–Tits group scheme.
- `componentPoints` is not shown to equal KP's Iwahori subgroup `T(F)_0`
  (Definition 2.5.13), nor the Library's `torusNormIwahori`
  (`Langlands.Geometry.Building.KPZeroSubgroups`). The agreement with KP is
  a comparison of values: index `2`, and every point integral.
- The special fibre is not identified with `μ₂ × G_a` as a scheme, and its
  neutral component is not computed. The sign is defined on `𝓀[F]`-points
  only. `componentPoints` is not compared with any neutral-component
  subgroup in the Library.
- No building and no point `x` appear.
- Residue characteristic `2`, where `X ^ 2 - ϖ` gives a wildly ramified
  extension, is excluded by `isUnit_two`; there `1 / 2` is not available and
  the trace criterion is not applied.
