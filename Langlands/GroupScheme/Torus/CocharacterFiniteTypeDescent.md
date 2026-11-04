# Bounded purely inseparable descent of multiplicative points

Module `Langlands.GroupScheme.Torus.CocharacterFiniteTypeDescent`,
namespace `Langlands.GroupScheme.CocharacterDatum`.

Let `k : Type u` be a field and let `Z` be a commutative group scheme over
`Spec k`. For a commutative `k`-algebra `S : Type u` and an additive
commutative group `Λ : Type u`, `multiplicativePoints Z S Λ` is the
subgroup of `Z(S[Λ])` consisting of points satisfying `IsMult`. Here
`S[Λ]` is `AddMonoidAlgebra S Λ`, and `IsMult` is the multiplicativity
identity defined in `Torus.CocharacterDatum`. Closure under the group
operations is supplied by that module. A `k`-algebra map `f : S →ₐ[k] S'`
induces the group homomorphism `multiplicativeCoeffMap f` by coefficient
extension.

For the descent results, assume that `Z` is affine and its structure
morphism is locally of finite type, and that `Λ` is torsion free.
Let `F` and `L` be fields in `Type u`, with compatible `k`-algebra and
`F`-algebra structures. Let `p` be the exponential characteristic of `k`,
and suppose there is an `e : ℕ` such that every `ℓ : L` satisfies
`ℓ ^ (p ^ e) ∈ (algebraMap F L).range`.
Then `multiplicativePointsEquivOfPowMemRange` is a group equivalence

```text
multiplicativePoints Z F Λ ≃* multiplicativePoints Z L Λ
```

whose forward map is coefficient extension along `F → L`.
There is no assumption that `L/F` is finite. The exponent bound is
uniform over `L`. Smoothness, connectedness and perfectness are not
assumed.

The lemma `IsMult.coeffMap_tensor_eq` proves that a multiplicative point
over `L[Λ]` has equal images under the two inclusions into
`(L ⊗[F] L)[Λ]`. The lemma
`IsMult.exists_coeffMap_eq_of_pow_mem_range` recovers a multiplicative
point over `F[Λ]` whose coefficient extension is the original point.
Injectivity of coefficient extension gives the equivalence.
The final lemma `IsDatum.exists_of_pow_mem_range_of_finiteType` recovers
a datum of the same character and weight, again with coefficient
extension equal to the original point.

The proof follows the tensor equalizer argument in
`Torus.CocharacterInseparableDescent`. Form the quotient `v` of the two
tensor-valued images of the point. Folding the tensor product onto its
right factor sends `v` to the identity. The bounded-power hypothesis
and `CommutativeFrobenius.affinePoints_pow_eq` therefore show that
`v ^ (p ^ e) = 1`. Multiplicativity identifies that power with the map
on points induced by multiplication by `p ^ e` on the exponent group.
This exponent map is injective because `Λ` is torsion free and
`p ^ e ≠ 0`. Consequently `v = 1`.

The published coefficient equalizer lemma
`CocharacterDescent.exists_mapAlgHom_ofId_eq_of_includeLeft_eq_includeRight`
then recovers every coordinate in `F[Λ]`. The affine-point descent lemma
assembles them into a point over `F[Λ]`. Multiplicativity and the datum
conditions are reflected along the injective coefficient map, by
`IsMult.of_coeff_map` and `IsDatum.of_coeff_map`.

This is an internal construction and deduction from the published
cocharacter coordinate and tensor equalizer APIs, together with the
commutative Frobenius power theorem. It strengthens the earlier
conditional descent result by proving its separate power premise from
finite type, preserving the original point and constructing a group
equivalence. It does not assert unipotence or maximal-torus base change.
