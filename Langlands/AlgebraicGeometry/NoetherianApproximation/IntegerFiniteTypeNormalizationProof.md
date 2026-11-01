# Finite normalization of finite type integer domains

`integerFiniteTypeNormalization` proves exactly
`IntegerFiniteTypeNormalizationStatement` at arbitrary universe, with no outer
assumptions. For every domain A of finite type over the integers, its integral
closure in its own fraction field is finite as an A-module.

The proof splits by the characteristic of A. In prime characteristic, A is a
finite type algebra over the finite prime field. Field Noether normalization
gives a finite injective map from a polynomial algebra, which is normal and
noetherian. The normal-subbase theorem gives finite normalization. That theorem
removes the separability restriction on fraction-field extensions by bounding
the purely inseparable part with a Frobenius iterate; the finite Frobenius map
and noetherian submodules give the required module finiteness.

In characteristic zero, `finite_normalization_of_charZero` applies the chart
construction at every maximal ideal q. The closed fibre over the contracted
integer prime admits field Noether normalization. Lifting its variables gives
a polynomial map whose injectivity follows from successive division in the
kernel and Krull intersection. The finite closed fibre gives quasi-finiteness
at q. Zariski Main Theorem then produces a subalgebra C finite over the integer
polynomial ring and an element r of C outside q such that C[1/r] → A[1/r] is
bijective. The normal-subbase theorem gives finite normalization of C.

The normalization-localization helper transfers this finite normalization to
the canonical localized A-module
`LocalizedModule.Away r.val (integralClosure A (FractionRing A))`.
It identifies the fraction fields through the chart map and uses compatibility
of integral closure with localization. Since every maximal ideal omits some
such r, these elements generate the unit ideal. The module local-to-global
criterion proves finite generation of the original normalization over A.

`integerFiniteTypeNormalization_of_charZero` packages the characteristic split;
the final theorem supplies its characteristic-zero argument just proved. All
subbase, finiteness, localization and chart assumptions are constructed inside
the proof. This is an internal derivation from Mathlib's field Noether
normalization, finite integral-closure theorem, Frobenius, Krull intersection,
Zariski Main Theorem and localization results. The paired helper files describe
their implemented proofs in detail. Workers 74 and 706 developed the chart and
normalization arguments jointly.
