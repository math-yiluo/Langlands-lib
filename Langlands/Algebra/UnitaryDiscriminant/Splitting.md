# Finite Galois splittings and the discriminant class without a supplied chart

Module `Langlands.Algebra.UnitaryDiscriminant.Splitting`, namespace `Langlands.UnitaryDiscriminant`.

The discriminant class `discriminantClass hι hτ e` of
`Langlands.Algebra.UnitaryDiscriminant.Class` takes a finite Galois matrix splitting chart `e` as
input. This module shows that such a chart exists for every central simple algebra, and defines
the class directly from the algebra and its involution by choosing one.

## Declarations

* `GaloisSplitting F L B n` (structure). For fields `F L : Type u` with `Algebra F L` and an
  `L`-algebra `B`, it bundles a field `field : Type u` with instances `Field`, `Algebra F`,
  `Algebra L`, `IsScalarTower F L`, `FiniteDimensional F` and `IsGalois F`, and an algebra
  isomorphism `chart : field ⊗[L] B ≃ₐ[field] Matrix (Fin n) (Fin n) field` over `field`.
  These are exactly the inputs `M` and `e` of `discriminantClass`. The instance fields are
  registered as instances.
* `bundledCSA L B : CSA.{u, u} L` is `B` as a bundled central simple algebra.
* `reducedDegree_eq_of_finrank`: if `finrank L B = n²` then the Library's
  `CentralSimple.reducedDegree L B` is `n`.
* `galoisSplitting F L B hB : GaloisSplitting F L B n`, for
  `[FiniteDimensional F L] [Algebra.IsSeparable F L]`, a finite-dimensional central simple
  `L`-algebra `B : Type u` and `hB : finrank L B = n ^ 2`.
* `exists_galoisSplitting`: such a splitting exists.
* `discriminantClassOf hι hτ hB : BrauerGroup.{u, u} F`, for `L/F` separable quadratic,
  `ι ≠ 1`, `hτ : IsUnitaryInvolution ι τ` and `hB : finrank L B = (2m)^2`. It is
  `discriminantClass hι hτ (galoisSplitting F L B hB).chart` (`discriminantClassOf_eq`). It takes
  only the actual algebra, its involution and the degree, so it applies to every central simple
  `L`-algebra of degree `2m` with a unitary involution, split or not, for example a division
  algebra.
* `two_nsmul_discriminantClassOf`: this class is killed by two.

## Construction of the splitting

1. `E = CentralSimple.finiteGaloisSplittingField L B` is the Library's finite Galois extension of
   `L` with the chart `CentralSimple.finiteGaloisSplittingChart L B` of size
   `reducedDegree L B`. Its size is `n` by `reducedDegree_eq_of_finrank`, since
   `finrank L B = reducedDegree L B · reducedDegree L B` (`finiteGaloisSplittingChart_spec`).
2. `E` becomes an `F`-algebra through `L`. Then `E/F` is finite (`Module.Finite.trans`) and
   separable (`Algebra.IsSeparable.trans`), hence algebraic.
3. `IsAlgClosed.lift` embeds `E` into `AlgebraicClosure F` over `F`. The splitting field is the
   normal closure `IntermediateField.normalClosure F E (AlgebraicClosure F)`. It is finite over `F`
   (`normalClosure.is_finiteDimensional`) and Galois over `F`
   (`IsGalois.normalClosure_of_isSeparable`, because `E/F` is separable and the algebraic closure is
   normal over `F`). It receives `E` (`normalClosure.algebra`), hence `L`, compatibly with `F`.
4. The chart is the Library's extension of the splitting chart along `E → field`
   (`BrauerComparison.enlargedSplittingChart`), followed by reindexing `Fin (reducedDegree L B)`
   to `Fin n` (`Matrix.reindexAlgEquiv`).

## Scope and provenance

Provenance: internal. That every central simple algebra is split by a finite Galois extension of
the base field containing its center is standard. Here it is assembled from the Library's finite
Galois splitting theorem over `L` and Mathlib's normal closures. The choice made in
`galoisSplitting` is one particular splitting. This module does not prove that
`discriminantClassOf` agrees with `discriminantClass` computed in another splitting. `B` is in the
same universe as `F` and `L` here, because the Library's splitting field and bundled central simple
algebras are; `discriminantClass` with a supplied chart allows any universe for `B`.
