# Depth-zero data for a norm-one torus over a local field

This module gives the anisotropic-torus regression example for the
depth-zero layer of `Langlands.BruhatTits.IntegralModels`. Earlier modules
state results for supplied `D : RelativeComponentModelData R K G` and
`Q : SpecialFibreQuotientData D`. Here both are constructed for the
norm-one torus `G = R¹_{E/F} G_m` of a finite separable field extension
`E / F` of a nonarchimedean local field `F`, from an integral form `B` of `E`.

The integral form is supplied data, not constructed:

- `B` is a finite free `𝒪[F]`-algebra with an `F`-algebra isomorphism
  `eF : F ⊗[𝒪[F]] B ≃ₐ[F] E`;
- `eκ : 𝓀[F] ⊗[𝒪[F]] B ≃ₐ[𝓀[F]] k'` for a field `k'`, so that `k' / 𝓀[F]`
  is the residue extension;
- `hB` states that the norm-one kernel of `B` is smooth over `𝒪[F]`. The
  module proves `hB` whenever `B` splits as a product of copies of `A'` after
  a faithfully flat base change `𝒪[F] → A'`
  (`WeilGm.normOne_smooth_of_decomposition`).

The intended instance is an unramified extension `E / F` with `B` its ring
of integers. That instance is not formalized, and no concrete `B` is
constructed in this module.

From these data the module proves:

- the norm-one kernel `R¹_{B/𝒪[F]} G_m` is an integral model of `G`, with
  special fibre the norm-one torus `R¹_{k'/𝓀[F]} G_m`, which is connected
  reductive;
- the identity is a reductive quotient of the special fibre;
- `G(F)^{0+}` is the congruence subgroup of this model;
- the index of `G(F)^{0+}` in `G^0(𝒪)` is the number of norm-one units of
  `k'`. Multiplied by `q - 1`, it equals `q ^ n - 1`, where
  `q = Nat.card 𝓀[F]` and `n = [k' : 𝓀[F]]`. For `n = 2` the index is
  `q + 1`;
- `G` is anisotropic over `F`.

## Provenance

The module is derived. Its statements are standard facts about the norm-one
torus of an unramified extension and its smooth integral model. Here they
are obtained by applying published Library results to the supplied data.

The task objective (Task 3557, section "Regression examples") asks for a
proved example of an anisotropic group.

The comparison values come from Kaletha–Prasad, *Bruhat–Tits Theory: A New
Approach* (2023). The registered original is
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
The authors' corrections of 1 November 2024 are
`kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`.

- Definition 2.5.13 (printed p. 90 / PDF p. 121) defines the Iwahori
  subgroup `T(k)_0` of a torus `T`.
- Remark 2.5.15 is replaced by the corrections (Section 2.5, PDF pp. 24–25).
  The corrected remark treats the kernel `T` of the norm map
  `R_{ℓ/k} G_m → G_m` for a separable quadratic extension `ℓ / k`. It gives
  `T(k)_1 = T(k) = ℓ¹` and `T(k)_0 = o_ℓˣ / o_kˣ ⊂ ℓˣ / kˣ = T(k)`, with
  equality when `ℓ / k` is unramified. This is the case modelled here, with
  `ℓ = E`.
- 13.2.6 (printed p. 470 / PDF p. 501) identifies `P_{x,0} / P_{x,0+}` with
  the `f`-points of the maximal reductive quotient of the special fibre. For
  the unramified norm-one torus that quotient is `R¹_{f'/f} G_m`, with
  `(q ^ n - 1) / (q - 1)` points over `f`, and `q + 1` points when `n = 2`.

The corrections amend Remark 2.5.15 as above. They do not amend
Definition 2.5.13 or 13.2.6: in Chapter 13 (PDF p. 49) they amend only
13.5.2, 13.6.2 and 13.8.5.

KP's objects are not used in the Lean statements. The module computes the
Library's `D.neutral.integralPoints`, `Q.positivePoints` and the index for
the constructed data. The KP values above are the values these results are
compared against.

## Setting

`F` is a field in universe `u` with `ValuativeRel F`, `TopologicalSpace F`
and `IsNonarchimedeanLocalField F`. `𝒪[F]` is its valuation ring and `𝓀[F]`
its residue field. The generic group is
`WeilGm.normOne (CommRingCat.of F) E`, the published kernel of the norm
`R_{E/F} G_m → G_m`.

The section variables of the local-field part are:

- `B : Type u` with `[CommRing B] [Algebra 𝒪[F] B] [Module.Finite 𝒪[F] B]
  [Module.Free 𝒪[F] B]`;
- `E : Type u` with `[Field E] [Algebra F E] [FiniteDimensional F E]`, and
  `eF : F ⊗[𝒪[F]] B ≃ₐ[F] E`;
- `hB : Smooth (normOne (CommRingCat.of 𝒪[F]) B).X.hom`;
- `k' : Type u` with `[Field k'] [Algebra 𝓀[F] k']`, and
  `eκ : 𝓀[F] ⊗[𝒪[F]] B ≃ₐ[𝓀[F]] k'`;
- from `normOneModelData` on, `[Algebra.IsSeparable F E]`.

The file sets `backward.isDefEq.respectTransparency` and
`backward.isDefEq.respectTransparency.types` to `false`, as do the imported
modules.

## Declarations

### General norm-one kernels (namespace `Langlands.GroupScheme.WeilGm`)

Here `A` is a commutative ring and `B`, `B'` are finite free `A`-algebras.

- `kerCongr` (private): a commuting square of group isomorphisms restricts
  to an isomorphism of kernels. The Library has the same helper as the
  private `kernelModelEquiv` in two modules, which cannot be imported.
- `tensorNorm_congr`, `tensorNormUnits_congr`: the published
  `Langlands.Algebra.tensorNorm A B R` and `tensorNormUnits` are unchanged
  by an `A`-algebra isomorphism `e : B ≃ₐ[A] B'` applied to the first
  tensor factor (Mathlib's `Algebra.norm_eq_of_algEquiv`).
- `normOneCongrUnitsEquiv e R` (definition), with `_val` and
  `_naturality`: the induced isomorphism of norm-one units, built from the
  published `tensorUnitsEquiv e R`, and its compatibility with restriction
  along test morphisms.
- `normOneCongrIso e : normOne A B ≅ normOne A B'` (definition), with
  `normOneCongrIso_hom_points`. It is built with the published
  `isoOfPointModels` from the published `normOnePointsEquiv`.
- `normOneCoeffEquiv A B g` (definition), with `_val`: for an `A`-algebra
  isomorphism `g : S ≃ₐ[A] T`, norm-one units of `B ⊗ S` and `B ⊗ T`
  correspond (via the published `tensorNormUnits_naturality`).
- `normOne_isAffineHom` (instance): `normOne A B` is affine over `Spec A`.
  It is a closed subgroup of the affine `R_{B/A} G_m`, as the kernel of a
  homomorphism into the separated `G_m`.
- `baseMap_fpqc`: for a faithfully flat `A`-algebra `A'`, `Spec A' → Spec A`
  is surjective, flat and quasi-compact.
- `normOne_smooth_of_decomposition`: if `e : A' ⊗[A] B ≃ₐ[A'] (I → A')`
  for a faithfully flat `A'` and a nonempty finite type `I`, then
  `normOne A B` is smooth over `Spec A`. Its base change is a split torus by
  the published `normOneDecompositionIso`, which is smooth, and Mathlib's
  fpqc descent of smoothness (`MorphismProperty.of_pullback_snd_of_descendsAlong`)
  gives the claim.

### The local-field data (namespace `Langlands.BruhatTits.IntegralModels`)

- `card_normOneUnits_mul K K'`: for fields `K`, `K'` with `K'` finite and
  `[Algebra K K']`, the kernel of the unit norm `K'ˣ → Kˣ` satisfies
  `Nat.card ker * (Nat.card K - 1) = Nat.card K' - 1`. The proof uses
  Mathlib's surjectivity of the norm on units of finite fields
  (`FiniteField.unitsMap_norm_surjective`).
- `normOneModel F B E eF hB` (definition): the
  `IntegralModel 𝒪[F] F (normOne (CommRingCat.of F) E)` with group
  `normOne (CommRingCat.of 𝒪[F]) B`. Its generic identification is the
  published `normOneAlgebraBaseChangeIso` followed by `normOneCongrIso eF`.
- `normOneModel_isSmooth`: the model is smooth (this is `hB`).
- `normOneSpecialFibreIso` (definition, given `[FiniteDimensional 𝓀[F] k']`):
  the special fibre is isomorphic to `normOne (CommRingCat.of 𝓀[F]) k'`.
- `isConnectedReductive_normOneSpecialFibre`: the special fibre is connected
  reductive. `k'` is finite-dimensional over `𝓀[F]` by `eκ`, and separable
  because `𝓀[F]` is finite. The published `normOne_isTorus_of_finite_separable`
  and `IsTorus.isConnectedReductive_of_fieldSplitting` apply.
- `normOneModelData` (definition): the
  `RelativeComponentModelData 𝒪[F] F (normOne (CommRingCat.of F) E)` given by
  the published `IntegralModel.relativeComponentData_of_reductive_localField`
  applied to `normOneModel`. The generic fibre is connected reductive since
  `E / F` is finite separable. `normOneModelData_neutral`: its neutral model
  is `normOneModel` (by `rfl`).
- `normOneQuotientData` (definition) and
  `normOneQuotientData_isReductiveQuotient`: the published identity quotient
  `SpecialFibreQuotientData.identityQuotient` and its `IsReductiveQuotient`
  proof, applied to `normOneModelData`.
- `residueSectionsEquiv F` (definition): global sections of `Spec 𝓀[F]`, as
  an `𝒪[F]`-algebra through the residue map, are `𝓀[F]`.
- `residueNormOneEquiv` (definition): norm-one units of `B ⊗ 𝓀[F]` are the
  kernel of `Units.map (Algebra.norm 𝓀[F] (S := k'))`, by `eκ`.
- `normOneSpecialFibrePointsEquiv` (definition): a group isomorphism from the
  `𝓀[F]`-points of the neutral special fibre to
  `(Units.map (Algebra.norm 𝓀[F] (S := k'))).ker`, the norm-one units of
  `k'`.
- `normOne_index_positivePoints_subgroupOf`: the index of
  `(normOneQuotientData ...).positivePoints.subgroupOf
  (normOneModelData ...).neutral.integralPoints` is the cardinality of that
  kernel. It uses the published
  `SpecialFibreQuotientData.localField_index_positivePoints_subgroupOf`.
- `normOne_index_positivePoints_subgroupOf_mul`: the same index times
  `Nat.card 𝓀[F] - 1` is `Nat.card 𝓀[F] ^ Module.finrank 𝓀[F] k' - 1`.
- `normOne_index_positivePoints_subgroupOf_of_finrank_eq_two`: if
  `Module.finrank 𝓀[F] k' = 2`, the index is `Nat.card 𝓀[F] + 1`.
- `normOne_isAnisotropic`: `IsAnisotropic (normOne (CommRingCat.of F) E)`,
  by the published `normOneAnisotropy`.
- `normOneQuotientData_radicalPoints`: the radical points are `⊥`.
- `normOneQuotientData_positivePoints`: `positivePoints` equals
  `(normOneModel F B E eF hB).congruenceSubgroup`, the image of the integral
  sections with trivial reduction.

## Scope

- No concrete `B` is constructed. The hypotheses `eF`, `eκ` and `hB` are not
  derived from a ramification condition on `E / F`.
- `G^0(𝒪)` is not computed. In particular, the module does not prove that
  every norm-one element of `E` is integral, which would give
  `T(k)_0 = T(k)` as in corrected Remark 2.5.15.
- No building and no point `x` appear. The constructed model is not
  identified with the Néron model or with a Bruhat–Tits parahoric group
  scheme. `G^0(𝒪)` and `G(F)^{0+}` are not identified with KP's `P_{x,0}`
  and `P_{x,0+}`. The agreement with the KP values above is only a
  comparison of numbers.
- Ramified norm-one tori are not treated.

The commuting-square kernel comparison reuses `WeilGm.kernelModelEquiv`
from [WeilRestrictionNormOne](../../GroupScheme/Torus/WeilRestrictionNormOne.md).
