# Iwasawa decomposition of the actual adelic `GL(n)` for the standard compact subgroup

This module proves that every element of the actual adelic group
`AdelicGL F n = GL(n, 𝔸_F)` is an upper triangular invertible matrix times an element of the
standard compact subgroup `standardCompact F n`. Equivalently, the pointwise product of the
Library's upper triangular subgroup `GeneralLinear.upperTriangularSubgroup n (Adeles F)` with
`standardCompact F n` is all of `GL(n, 𝔸_F)`. Here `F : Type u` is an arbitrary number field
and `n : ℕ` is arbitrary, including `n = 0`. The adele ring is the full
`Adeles F = AdeleRing (𝓞 F) F`.

`standardCompact F n` is defined in `Langlands.Global.AdelicGLStandardCompact` (accepted
candidate, bundled unchanged here). Its infinite component lies in the Library's
`standardInfiniteCompact F n`, which is real orthogonal at each real place and complex
unitary at each complex place. Its finite component lies in
`FiniteAdelicGL.standardIntegral F n`, where `g` and `g⁻¹` have integral entries at every
finite place.

## Provenance

Getz–Hahn, *An Introduction to Automorphic Representations* (2024), registered as
`getz-hahn-2024-automorphic-representations`, SHA256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`, §2.7, Theorem 2.7.1
and equation (2.24), printed p.71 (PDF p.88): for a parabolic subgroup `P ≤ G`, "There
exists a maximal compact subgroup `K ≤ G(A_F)` such that `G(A_F) = P(A_F)K`." The October 2026
errata (`getz-hahn-2024-errata-2026-10`) list no corrections for Chapter 2.

This module proves the covering equation (2.24) for `G = GL(n)` over a number field, in
matrix form. `P` is the upper triangular (Borel) subgroup and `K` is the explicit subgroup
`standardCompact F n`. The parabolic factor is on the left, as in (2.24). The maximality of
`K` is proved in the separate candidate module `AdelicGLStandardCompactMaximal`, not here.
The statement is a derived specialization. It is stated for matrix groups, not for the
actual adelic points of a group scheme with a parabolic subgroup scheme. The proof route
below is internal to the project.

## Finite places

* `exists_local_iwasawa F n v g`: at a finite place `v`, every `g ∈ FiniteLocalGL F n v =
  GL(n, F_v)` is `b k` with `b` upper triangular and `k ∈ FiniteAdelicGL.localIntegral F n v`
  (that is, `k` and `k⁻¹` have entries in the completion integers). For `n = 0` take
  `b = g`, `k = 1`. For `n = m + 1` this is the Library's
  `GeneralLinear.Iwasawa.exists_upperTriangular_mul`, applied to the valuation `Valued.v`
  of the completion. Its integral factor is the image of a matrix unit over the valuation
  integers. The entries of that image and of its inverse are integral, and the valuation
  integers coincide with the completion integers by definition.
* `exists_finite_iwasawa F n g`: every `g` in the actual finite adelic group is `β κ` with `β`
  upper triangular and `κ ∈ FiniteAdelicGL.standardIntegral F n`. For each finite `v`, set
  `b'_v = 1` if the local component `g_v` is in `GL(n, O_v)`, and otherwise take the local
  upper triangular factor `b_v` of `g_v`. Since `g_v ∈ GL(n, O_v)` for cofinitely many `v`
  (`FiniteAdelicGL.eventually_localIntegral`), the family `(b'_v)` lies in the actual
  restricted product `FiniteAdelicGL.LocalRestrictedProduct F n`. Then `β` is its image under
  the inverse of the Library's homeomorphism `FiniteAdelicGL.restrictedProductEquiv F n`,
  and `κ = β⁻¹ g`. Every local component of `β` is upper triangular, so `β` is. The local
  component of `κ` at `v` is `g_v` or the local integral factor `k_v`. So `κ` is in
  `standardIntegral` by `FiniteAdelicGL.mem_standardIntegral_iff_local`.

## Infinite places

* `exists_infinite_iwasawa F n h`: every `h` in the actual infinite adelic group is `β κ`
  with `β` upper triangular and `κ ∈ standardInfiniteCompact F n`. The proof is the first half
  of `exists_infinite_factorization` of `AdelicGLStandardCompact`, without its bounds. In the
  Library's coordinates `archimedeanGLCoordinates F n` it takes, at each real and each
  complex place, the triangular–unitary factorization `exists_upperTriangular_mul_unitary`
  of the accepted `TriangularUnitary` module. The unitary factors assemble to
  `κ = ArchimedeanCompactFactors.toInfiniteAdelicGL F n p`, which lies in
  `standardInfiniteCompact F n`. Then `β = h κ⁻¹` has the upper triangular factor as its
  coordinate at each place, by `local_mul_inv` and `mul_inv_val_eq`. Below-diagonal entries
  are zero, by injectivity of `NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace`. This
  theorem does not need `[NumberField F]`.

## Assembly

* `IsStandardIwasawaFactorization F n g β κ` is the proposition
  `g = β * κ ∧ β ∈ GeneralLinear.upperTriangularSubgroup n (Adeles F) ∧
  κ ∈ standardCompact F n`.
* `exists_isStandardIwasawaFactorization F n g`: every `g : AdelicGL F n` has such a
  factorization. Apply the infinite and finite results to `AdelicGL.infinite F n g` and
  `AdelicGL.finite F n g`, then combine the factors with `AdelicGL.pair`. The product
  identity is checked after the multiplicative homeomorphism `AdelicGL.split F n`.
  Membership in `standardCompact` is `mem_standardCompact_iff`.
* `upperTriangular_mul_standardCompact F n`: the pointwise product of
  `GeneralLinear.upperTriangularSubgroup n (Adeles F)` and `standardCompact F n`, as subsets
  of `AdelicGL F n`, is `Set.univ`.

## Scope

No uniqueness of the factorization, no bounds on the factors, and nothing about group
schemes, other parabolic subgroups or groups other than `GL(n)` is asserted. The general
reductive reduction target remains open.
