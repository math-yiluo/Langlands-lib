# The unitary norm theorem over number fields

Module: `Langlands.Algebra.CentralSimple.NumberFieldUnitaryNormStatement`.

`Langlands.CentralSimple.NumberFieldUnitaryNormStatement.{u}` is a proposition; this
module states it and does not prove it.

## The statement

It quantifies over the same data as
`Langlands.CentralSimple.NumberFieldLandherrStatement`: a number field `F`, a
separable quadratic extension `E/F`, a finite-dimensional central simple
`E`-algebra `B` that is an `F`-algebra through `E`, and an `F`-linear involution
`τ` of `B` acting on `E` by `SU3Root.conjugation F E`, the nontrivial automorphism.

For `z : Eˣ` it assumes that at every place `v` of `F`, with
`K_v = Global.placeCompletion F v`, there is a unit `x` of `K_v ⊗[F] B` with
`x ∈ unitaryPoints τ K_v` (that is, `x * τ_{K_v}(x) = 1`) and
`relativeNorm F E B K_v x = z ⊗ 1` in `E ⊗[F] K_v`. Here
`Langlands.CentralSimple.UnitaryPoints.relativeNorm` is the reduced norm of `B` over
`E` with coefficients in `E ⊗[F] K_v`. The conclusion is that there is a unit `x` of
`B` with `x * τ x = 1` and `reducedNorm E B E (1 ⊗ x) = z`, the reduced norm of `x`
over `E`.

## Source

Platonov and Rapinchuk, *Algebraic Groups and Number Theory* (1994), §6.7,
Theorem 6.28, printed p. 360 (PDF p. 370): "Let `y ∈ L*` and `N_{L/K}(y) = 1`.
Assume that for all `v` in `V^K` the equation `Nrd_{A/L}(x) = y` has a solution
`x_v` in `A ⊗_K K_v` such that `x_v τ(x_v) = 1`. Then this equation has a solution
`x` in `A*` such that `x τ(x) = 1`." There `K`, `L` and `A` are `F`, `E` and `B`.
The same statement is Proposition a of Kneser, *Lectures on Galois Cohomology of
Classical Groups* (1969), §5.6, printed p. 78 (PDF p. 84).

The source's hypothesis `N_{L/K}(y) = 1` is not repeated, because it follows from
the local hypothesis at any one place: for `x` with `x τ(x) = 1`, the reduced norm
satisfies `Nrd(τ x) = σ(Nrd x)` with `σ` the conjugation of `E`, so
`Nrd(x) σ(Nrd(x)) = 1`, and `E` embeds in `E ⊗[F] K_v`. The statement is therefore
equivalent to the source's. The local solutions are units, as `x τ(x) = 1` forces.
