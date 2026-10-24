# The integer permutation lattice on infinite places

Let `F : Type u` and `E : Type v` be fields with an `F`-algebra structure
on `E`, and put `G = E ≃ₐ[F] E`. The universes are independent.
`infinitePlaceLatticeRepresentation F E` uses Mathlib's `Rep.ofMulAction`
on the actual infinite places of `E`, with scalar ring
`NormalizedTwoCocycle.CoefficientScalars.{v} = ULift.{v} ℤ`.
Its carrier is the free module on these places, implemented as
`MonoidAlgebra (ULift ℤ) (InfinitePlace E)`. No multiplication on the set
of places is used. The basis action is `g(e_w) = e_(g • w)`.

The place action is Mathlib's arithmetic action: `g • w` is `w`
precomposed with the inverse field automorphism. Consequently the
coefficient at `w` of `g(x)` is the coefficient of `x` at `g⁻¹ • w`.
The two named action theorems prove these formulas directly from
Mathlib's permutation representation. This part requires no number-field,
Galois, or cyclicity hypothesis.

When `E` is a number field, the type of infinite places is finite.
`infinitePlaceLatticeFunctionEquiv` identifies the carrier linearly with
`InfinitePlace E → ULift ℤ`, and its action theorem gives the same
inverse-precomposition formula in function coordinates. The published
ring equivalence `NormalizedTwoCocycle.coefficientScalarsEquiv` identifies
the coefficient ring with `ℤ`, so these coordinates describe the usual
integer permutation lattice, with a universe lift.

`infinitePlaceLatticeSum` sums these finite coordinates. The proof of
`infinitePlaceLatticeSum_action` reindexes the sum by the permutation
`w ↦ g⁻¹ • w`. `infinitePlaceLatticeAugmentation` packages this invariant
linear map as a morphism to the trivial representation on the same
lifted integers. `infinitePlaceLatticeCohomology` denotes Mathlib's
ordinary `groupCohomology` of the permutation representation in every
natural degree; it introduces no alternative cohomology theory.

The source is Milne, *Class Field Theory*, v4.03 (2020), Chapter VII,
proof of Proposition 3.1, printed page 209 (PDF page 218). Specialize
its finite set `T` to all infinite places of `E`. Milne defines the
first lattice as `Hom(T, ℤ)`, with `(g f)(w) = f(g⁻¹w)`, and uses the
coordinate-sum hyperplane in the ambient real representation. The
finite free-module realization, universe lift, ordinary-cohomology
alias, and equivariant augmentation are derived implementation details.
This module proves no Herbrand quotient formula, cohomology finiteness,
Dirichlet lattice comparison, or unit or idele-class theorem.

Registered source: `milne-2020-class-field-theory`,
`/home/taskhub/central-library/Milne--Class Field Theory (v4.03)--2020.pdf`.
