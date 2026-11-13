# Normal finite-type two-axis extension from class representability

Worker 198 wrote this internal reduction for Task 5678.

`Langlands.AbelianScheme.normalFiniteTypeTwoAxisExtensionProperty_of_twoAxisClassRepresentability`
has type

`NoetherianTwoAxisClassRepresentabilityStatement.{u} →
NormalFiniteTypeTwoAxisExtensionProperty.{u}`.

It is a conditional theorem. It does not prove either proposition.

## Proof

Let `T` be an integrally closed domain of finite type over `ℤ`, and `B` an actual
abelian scheme over `Spec T`. Let `N` be an actual line bundle on the
self-product of the base change of `B` to `FractionRing T`, with both unit-axis
restrictions trivial.

1. `T` is noetherian by Mathlib's `Algebra.FiniteType.isNoetherianRing ℤ T`.
2. The hypothesis supplies `q : Y ⟶ Spec T`, separated, locally of finite type
   and formally unramified, with a representation `e` of the published
   `classPresheaf B`.
3. `discreteValuativeExistence_of_representableBy B q e`, from
   `TwoAxisValuationClassSurjectivity`, gives the discrete valuative existence
   condition for `q`.
4. The published `actualBundleExtension_of_normal_discreteValuativeExistence`,
   from `TwoAxisClassSectionExtension`, takes `R = CommRingCat.of T`,
   `K = FractionRing T`, `B`, `q`, `e`, that condition, `N` and both axis
   trivialities. It returns an actual line bundle `E` on the total self-product
   and an actual module-sheaf isomorphism from its pullback along
   `mumfordProductBaseChangeMap B (Spec.map (algebraMap T (FractionRing T)))` to
   `N`. This is exactly the conclusion of the target proposition, with its
   canonical map `b`.

No polarization, dual, projectivity, regularity or dimension hypothesis is added.
The provenance is internal composition of the Library results named above.
