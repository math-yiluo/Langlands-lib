# Normal finitely generated subalgebras

`Langlands.AlgebraicGeometry.NoetherianApproximation.normalFiniteTypeSubalgebra`
proves exactly `NormalFiniteTypeSubalgebraStatement.{u}`, with no outer
hypotheses. For every integrally closed commutative domain `R : Type u` and
every finite subset `s`, it produces an integer subalgebra `T` of `R` that
is finitely generated over the integers, contains `s`, is integrally closed
in its own fraction field, and is noetherian. The universe, characteristic,
and dimension are unrestricted.

The implemented proof applies `integerFiniteTypeNormalizationReduction` to
`integerFiniteTypeNormalization`, both imported from their published modules.
The second theorem proves that every finite type integer domain has
module-finite normalization in its own fraction field. Its proof splits
by characteristic, using finite-field Noether normalization and Frobenius
in prime characteristic, and polynomial charts, Zariski Main Theorem,
localization, and finite-generation patching in characteristic zero.

The reduction forms `A = ℤ[s]` inside `R` and normalizes `A` in `Frac A`.
The finiteness theorem makes that normalization finite type over the
integers. The inclusion `A → R` extends to an injection `Frac A → Frac R`.
Integral closedness of `R` places the normalization's image inside `R`,
giving an injective integer algebra map. Its range is the required `T`.
The reduction proves containment of `s`, transports integral closedness
across the range equivalence, and obtains noetherianity from finite
generation over the integers.

This is an internal composition of the two published proofs. Their paired
Markdown files explain the implemented arguments and the original-source
provenance of the statement. The finite-normalization premise of the
reduction is discharged by the imported theorem; the final theorem has
the entire published target type.
