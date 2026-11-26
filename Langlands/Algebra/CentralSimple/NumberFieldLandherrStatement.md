# Landherr's theorem over number fields

Module: `Langlands.Algebra.CentralSimple.NumberFieldLandherrStatement`.

`Langlands.CentralSimple.NumberFieldLandherrStatement.{u}` is a proposition; this
module states it and does not prove it.

## The statement

It quantifies over types `F E B : Type u` with:

- `F` a number field and `E` a field with `Algebra F E`,
  `Algebra.IsQuadraticExtension F E` and `Algebra.IsSeparable F E`;
- `B` a ring with `Algebra E B`, `Algebra F B`, `IsScalarTower F E B`,
  `FiniteDimensional E B`, `Algebra.IsCentral E B` and `IsSimpleRing B`, that is, a
  finite-dimensional central simple `E`-algebra that is an `F`-algebra through `E`;
- an `F`-linear involution `τ : Quaternionic.FirstKindInvolution F B` that acts on
  `E` by the nontrivial automorphism: for every `e : E`,
  `τ (algebraMap E B e) = algebraMap E B (SU3Root.conjugation F E e)`, where
  `SU3Root.conjugation F E` is the unique nonidentity `F`-automorphism of `E`.
  This is an involution of the second kind (a unitary involution).

For a unit `y : Bˣ` with `τ y = y`, it assumes that at every place `v` of `F`
(`Global.Place F`, archimedean and finite), with `K_v = Global.placeCompletion F v`
the actual completion, there is a unit `x` of `K_v ⊗[F] B` with
`1 ⊗ y = x * (τ.baseChange K_v) x`. The conclusion is that there is a unit `x` of
`B` with `y = x * τ x`.

## Source

Platonov and Rapinchuk, *Algebraic Groups and Number Theory* (1994), §6.7,
Theorem 6.27 (Landherr), printed p. 359 (PDF p. 369): "Suppose `y ∈ A*` is
symmetric. Assume for each `v` in `V^K` the equation `y = x τ(x)` has a solution
`x_v` in `A ⊗_K K_v`. Then this equation has a solution `x` in `A*`." There `K` is
a number field, `L/K` a quadratic extension and `A` a central simple `L`-algebra
with an involution `τ` of the second kind; in this statement these are `F`, `E/F`
and `B`. The same statement is Landherr's theorem (second formulation) in Kneser,
*Lectures on Galois Cohomology of Classical Groups* (1969), §5.5, printed p. 77
(PDF p. 83).

The local solutions are taken to be units of `K_v ⊗[F] B`. This is no restriction:
`y` is a unit, so `x_v τ(x_v)` is a unit of the finite-dimensional algebra
`K_v ⊗[F] B`, and then `x_v` is a unit. The completions at all places, archimedean
and finite, are used, as in the source.
