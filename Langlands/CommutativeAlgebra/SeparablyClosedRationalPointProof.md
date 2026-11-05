# Proof: rational points of geometrically reduced algebras over separably closed fields

Authors: Worker 254 (Lean proof and documentation), Worker 1530 (submission).

This module proves the Library statement
`Langlands.CommutativeAlgebra.SeparablyClosedRationalPointStatement.{u,v}`.
The new declarations live in the namespace
`Langlands.CommutativeAlgebra.SeparablyClosedRationalPointProof`. It imports
the statement module, the helper modules
`Langlands.CommutativeAlgebra.RationalPointSpecialization` and
`Langlands.CommutativeAlgebra.GeometricallyReducedSeparatingBasis`, the published
`PointTopology.SmoothSeparablyClosedDensity` infinitude lemma, and Mathlib.

## Main result

`separablyClosedRationalPoint : SeparablyClosedRationalPointStatement.{u, v}`,
for arbitrary universes `u` and `v`. For every field `k : Type u` with
`[IsSepClosed k]` and every nontrivial commutative `k`-algebra `R : Type v` that
is of finite type and geometrically reduced over `k`, there is a `k`-algebra
map `R →ₐ[k] k`.

## Auxiliary results

- The imported `Langlands.AlgebraicGeometry.PointTopology.infinite_of_isSepClosed`
  shows that a separably closed field is infinite.
- `isGeometricallyReduced_localization`: every localization `Localization M`
  of a geometrically reduced algebra over a field `k` is geometrically reduced
  over `k`.
- `nonempty_algHom_of_field`: let `k` be separably closed and `K` a field
  extension of `k` that is essentially of finite type and geometrically
  reduced. Then every finite-type `k`-algebra `R` with a `k`-algebra map
  `R →ₐ[k] K` has a `k`-algebra map `R →ₐ[k] k`.

## Proof

The reused `PointTopology.infinite_of_isSepClosed`: if `k` is finite, it is perfect
(`PerfectField.ofFinite`). A separably closed perfect field is algebraically
closed (`IsSepClosed.isAlgClosed_of_perfectField`), and algebraically closed
fields are infinite. Either way `k` is infinite.

`isGeometricallyReduced_localization`. By
`Algebra.isGeometricallyReduced_field_iff` it suffices that
`AlgebraicClosure k ⊗[k] Localization M` is reduced.
`IsLocalization.tensorProductEquivOfMapIncludeRight` identifies it with a
localization of the reduced ring `AlgebraicClosure k ⊗[k] B`, and localizations
of reduced rings are reduced.

`nonempty_algHom_of_field`.

1. By `GeometricallyReducedSeparatingBasis.exists_isTranscendenceBasis_and_isSeparable`,
   `K` has a finite transcendence basis `s` over `k` such that `K` is separable
   over `F = k(s)` (`IntermediateField.adjoin k s`).
2. `K` is finite over `F`. It is essentially of finite type over `F`
   (`Algebra.EssFiniteType.of_comp`) and formally unramified, being separable
   (`Algebra.FormallyUnramified.of_isSeparable`). It is free over the field `F`.
   An essentially finite type, formally unramified, free algebra is finite
   (`Algebra.FormallyUnramified.finite_of_free`).
3. Let `P = k[s]` (`Algebra.adjoin k s`). Mathlib's scoped instances
   `IntermediateField.algebraAdjoinAdjoin` make `F` the fraction field of `P`,
   compatibly with `k`.
4. Since `s` is algebraically independent, `AlgebraicIndependent.aevalEquiv`
   identifies `P` with the polynomial ring `MvPolynomial s k`. A nonzero `D : P`
   corresponds to a nonzero polynomial. Since `k` is infinite and a domain,
   `MvPolynomial.funext` gives a point `x : s → k` where this polynomial does not
   vanish. Evaluation at `x` is a `k`-algebra map `P → k` that does not kill `D`.
5. This is the hypothesis `H` of
   `RationalPointSpecialization.nonempty_algHom_of_isFractionRing`, which gives
   the map `R →ₐ[k] k`.

`separablyClosedRationalPoint`.

1. Since `R` is nontrivial, `⊥ ≠ ⊤`, so `R` has a minimal prime `q`
   (`Ideal.nonempty_minimalPrimes`).
2. `R` is reduced (`Algebra.isReduced_of_isGeometricallyReduced`), so
   `Localization.AtPrime q` is reduced. It has Krull dimension `0`
   (`Ring.KrullDimLE.of_isLocalization`), and a reduced local ring of dimension
   `0` is a field (`Ring.KrullDimLE.isField_of_isReduced`). The proof installs
   this field structure as a local instance.
3. `Localization.AtPrime q` is essentially of finite type over `k` (a
   localization of a finite-type algebra) and geometrically reduced over `k`
   (`isGeometricallyReduced_localization`).
4. `nonempty_algHom_of_field`, applied to the localization map
   `R →ₐ[k] Localization.AtPrime q`, gives the map `R →ₐ[k] k`.

The theorem uses only the axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Provenance

The statement's Markdown derives it from Stacks Lemmas 33.25.7 (Tag 056V) and
33.25.6 (Tag 056U). The Lean proof does not use smoothness. It reduces to the
function field at a minimal prime, uses MacLane's criterion (in Mathlib) to get
a separating transcendence basis, and specializes a separable primitive element
along a `k`-point of affine space. This route and the helper lemmas are our own.
