# Categorical replacement of bounded flat complexes

This proof implements the internal algebraic assembly proposition
`BoundedFlatCategoricalReplacementStatement`.

The base ring `R` is commutative and noetherian. The input `C` is a
natural-number-indexed cochain complex of flat `R`-modules whose terms
vanish above a natural number `n`. Its degree-zero kernel and every
positive cycle module modulo the image of the preceding differential
are finitely generated over `R`; these are its degree-zero and positive
cohomology finiteness assumptions.

The proof first applies
`boundedFlatComplexProjective` to the actual modules and consecutive
differentials of the given natural-number-indexed complex. It packages
the resulting finite projective modules and linear maps as an actual
`CochainComplex` and a morphism into the original complex. The explicit
cycle and boundary tests give `QuasiIso` by `natModuleQuasiIsoCriterion`.
Extension by zero to integer degrees is strictly perfect by
`boundedNatComplexExtension`; the extended quasi-isomorphism becomes an
isomorphism under the standard derived localization.

The proof chooses that same extended complex before introducing any
scalar ring or homomorphism. For an arbitrary homomorphism `R →+* A`, it
uses `boundedFlatQuasiIsoBaseChange` to prove the four tests after tensoring
with `A`, and applies the categorical criterion again. It extends and
localizes this quasi-isomorphism, then uses `DerivedPlus.mapExtendIso` to
identify its source with the degreewise scalar extension of the chosen
integer-indexed complex. No flatness or noetherianity of `A` is assumed. The elaboration option
`backward.isDefEq.respectTransparency false`, also used in Mathlib’s
scalar-extension definitions, permits reduction of their induced scalar
actions when identifying the tensor maps; it adds no mathematical premise.

Worker 137 assembled this internal adapter from the named algebraic and
indexing prerequisites. Their separate paired documentation records the
external algebraic provenance. This proof uses actual Mathlib complexes
and derived objects in arbitrary carrier universe `u`. It does not
construct a scheme-derived-sections comparison or prove the geometric
universal-perfect-sections theorem.
