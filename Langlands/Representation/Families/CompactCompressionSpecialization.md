# Specializing compact-compression matrices

This internal adapter supplies the matrix comparison in the determinant
argument of Renard, *Représentations des groupes réductifs p-adiques*
(2026), VI.8.4, printed pp. 192–193 (PDF pp. 198–199).
It applies to actual smooth complex representations with a compatible
coefficient-ring action; it is independent of a choice of parabolic.

Let `R` be a commutative ring, `A` a smooth complex representation with
an `R`-action commuting with complex scalars and all group operators,
and `K` a compact open subgroup. Given a finite `R`-basis `b` of
`A`'s actual fixed vectors, `coefficientMatrix` records the coefficients
of the actual operator which acts by a group element and then applies
the normalized finite-orbit compact average.

For an evaluation `R → ℂ`, an actual complex intertwiner `f : A → B`
respecting evaluation of coefficients, and a bijection of the full
scalar extension with `B`, `specializedBasis` transports the scalar
extension of `b` to the actual fixed vectors of `B`. It uses the
published `Compact.CoefficientSpecialization.fixedScalarExtensionEquiv`.
That equivalence follows from the split compact average and does not
assume flatness of the evaluation map.

`specializedBasis_apply` identifies each specialized basis vector with
evaluation of the corresponding original vector.
`specializedBasis_repr` proves that its coordinates are evaluations
of the coefficient coordinates, using the tensor-product basis
coordinate formula.
`fixedMatrix_specializedBasis` then identifies the actual complex
compression matrix with entrywise evaluation of `coefficientMatrix`.
The proof uses the published naturality of `Jacquet.compressedAction`
under the intertwiner `f`.

All module, compatibility, basis, and full-specialization premises are
explicit. This unit proves a matrix comparison; it does not construct
an induced family, supply its finite free basis, establish the full
specialization bijection for it, or prove a uniform detector.
