# Quotient descent from the principal-norm formula

This module proves the quotient step for the already constructed genuine
adelic and idelic norm. Its input is the exact arithmetic equation saying
that the norm of a principal adele is the principal adele of the determinant
field norm. That equation remains an explicit hypothesis of this module's
constructions. The unconditional principal formula and idele-class norm
are supplied by the separate published modules described below.

`ideleNorm_principal_of_principal_formula` applies equality of units to the
principal-adele equation. The resulting equation uses the actual field-unit
norm `Units.map (Algebra.norm K)` and Mathlib's actual principal-idele
embeddings. Using this unit equation, with the unit norm of `x` as the
witness, `ideleNorm_principal_le_of_principal_formula` proves that the raw
idelic norm maps the principal subgroup into the principal subgroup.

`ideleClassNormOfPrincipalFormula` applies `QuotientGroup.map` to this subgroup
inclusion. Its source and target are Mathlib's genuine idele-class groups.
Continuity follows from the quotient-map criterion: precomposing the descended
map with the source quotient map is the target quotient map composed with
the already continuous raw idelic norm. The representative equation is
definitional. The uniqueness theorem uses quotient induction to show that
any continuous homomorphism with the same representative equation equals
this construction.

`ideleClassNormOfFiniteTensorComparison` combines this descent with the
determinant reduction in `NormReduction.lean`. The only additional arithmetic
premise in this version is bijectivity of every canonical finite completed
tensor map. The infinite comparison is already proved in `Norm.lean`.
The finite premise remains explicit in this definition; no arbitrary map,
norm, or equivalence is supplied in its place. The fields `K : Type u` and
`L : Type v` have their field, number-field and `Algebra K L` instances,
with finite relative dimension inferred and both universes independent.
No Galois or abelian hypothesis is required.

`Langlands.Global.AdelicFunctoriality.completedTensorComparison` in
[CompletedTensorComparisonProof](CompletedTensorComparisonProof.md) proves
this finite premise as well as the infinite-place comparison.
`Langlands.Global.AdelicFunctoriality.normCompatibility` in
[NormCompatibilityProof](NormCompatibilityProof.md) proves the comparison
and principal-adele formula, using the determinant reductions in
[NormReduction](NormReduction.md).

[IdeleClassNorm](IdeleClassNorm.md) specializes the descent helpers with a
proved principal formula. In that module,
`Langlands.Global.AdelicFunctoriality.adeleNorm_principal` and
`Langlands.Global.AdelicFunctoriality.ideleNorm_principal` give the two
principal identities, and
`Langlands.Global.AdelicFunctoriality.ideleNorm_principal_le` gives subgroup
preservation. The actual continuous homomorphism is
`Langlands.Global.AdelicFunctoriality.ideleClassNorm`; its laws are
`Langlands.Global.AdelicFunctoriality.ideleClassNorm_mk`,
`Langlands.Global.AdelicFunctoriality.continuous_ideleClassNorm`,
`Langlands.Global.AdelicFunctoriality.ideleClassNorm_principal` and
`Langlands.Global.AdelicFunctoriality.ideleClassNorm_unique`.
These unconditional results leave the present module's conditional
interfaces unchanged and do not prove global reciprocity.

The original arithmetic source is Andre Weil, *Basic Number Theory*, second
edition (1973), Chapter III section 4, Theorem 4 and Corollary 3, printed
pp. 56-58 (PDF pp. 73-75), for completed tensor decomposition and its norm
identity; Chapter IV section 1, Corollary 3, printed p. 64 (PDF p. 81), for
the adelic product; and Chapter IV sections 3-4, printed pp. 71-76
(PDF pp. 88-93), for the idele topology and principal quotient. These
passages were read. Registered original: `weil-1973-basic-number-theory`,
SHA256 `32fff78f8ccc5d6378907941e26746c34e20fc3adf5096508844cfe8a301e33b`.
The quotient and continuity arguments above describe the implemented Lean
proof. This module is a conditional reduction; its arithmetic premise is
proved separately, and the cited source also contains results beyond these
norm and quotient constructions.
