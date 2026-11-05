# Central split-torus extensions with polynomial quotient coordinates

Worker 1575 adapted the published `CentralTorusExtensionHopf` module by
Worker 1395. This is an internal algebraic prerequisite for the characteristic-zero
factorization of commutative affine groups. It is derived from the existing
Library grading argument and Mathlib's Picard group and polynomial-unit results;
it is not asserted to be a separately sourced theorem from the literature.

Let `K` be any field, `A` a commutative Hopf algebra over `K`, `B` a
commutative bialgebra over `K`, and `J` an index type. The structure
`CentralTorusVectorExtensionHopf.IsCentralExtension φ π` records bialgebra maps
`φ : B → A` and `π : A → K[J → ℤ]`, with injective `φ`, surjective `π`,
trivial composite, central coaction through `π`, and every degree-zero
invariant in the image of `φ`. Geometrically these are coordinate conditions
for an extension with central split-torus kernel and quotient `Spec B`.
The structure is a proposition, and supplies no geometric hypotheses itself.

With trivial Picard group of `B`, `exists_unit_mem_grade` provides an `A`-unit
in each torus weight. The proof regards each component as a `B`-submodule
using `φ`. It reuses
`CentralTorusExtensionHopf.exists_mem_grade_counit_eq_one` for the
counit-normalized homogeneous element. The product of the degree `n` and degree `-n` submodules is `1`:
invariants give one inclusion, and the antipode identity from
`GroupAlgebraCoaction` gives the other. The resulting invertible submodule
has trivial Picard class, so `Submodule.ker_unitsToPic` makes it the span of
a unit. This part adapts the published proof by replacing its Laurent
polynomial quotient algebra with `B`.

For a homogeneous unit `u`, the linear map `divide` takes the degree `n`
part of `a`, multiplies it by `u⁻¹`, and lifts the invariant result through
`φ`. Centrality gives
`Δu = (φ ⊗ φ)(f) · (u ⊗ u)` for an element `f` of `B ⊗ B`.
Doing the same for `u⁻¹` and using injectivity of `φ ⊗ φ` shows that `f` is
a unit. Under the explicit assumption that every unit of `B ⊗ B` is scalar,
write `f = d · 1`. A counit identity gives `d ε(u) = 1`, and therefore
`d • u` is group-like. This normalization theorem does not require Picard
triviality.

For finite `J`, `weightSection` chooses group-like lifts on a basis of
`J → ℤ` and extends additively. `sectionMap` extends this homomorphism to
an actual bialgebra homomorphism `K[J → ℤ] → A` using
`AddMonoidAlgebra.lift`; its coalgebra laws follow from group-likeness.
`comp_sectionMap` proves `π ∘ sectionMap = id`. This constructs a retraction
of the central split-torus inclusion on spectra, assuming both Picard
triviality and the scalar-unit condition.

The accompanying `PolynomialTensorUnits.exists_eq_smul_one` proves the
scalar-unit condition for `B = MvPolynomial I K`, for any index type `I`.
It identifies the tensor square with the polynomial algebra on `I ⊕ I`
and applies `MvPolynomial.isUnit_iff_eq_C_of_isReduced` over the field.
Mathlib's unique factorization instance for a polynomial algebra over a
field supplies the trivial Picard group in applications.

This module constructs the algebraic section only. It does not yet provide
transport to arbitrary affine group schemes, descent for a nonsplit torus,
or the final rational-point factorization. There is no characteristic
restriction in these algebraic results.
