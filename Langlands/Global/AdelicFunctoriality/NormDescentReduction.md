# Quotient descent from the principal-norm formula

This module proves the quotient step for the already constructed genuine
adelic and idelic norm. Its input is the exact arithmetic equation saying
that the norm of a principal adele is the principal adele of the determinant
field norm. That equation is an explicit hypothesis, not a proved global
compatibility result. The module therefore does not yet give an unconditional
idele-class norm or complete the task.

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
The finite premise remains unproved; no arbitrary map, norm, or equivalence
is supplied in its place. Both field universes remain independent.

The original arithmetic source is Andre Weil, *Basic Number Theory*, second
edition (1973), Chapter III section 4, Theorem 4 and Corollary 3, printed
pp. 56-58 (PDF pp. 73-75), for completed tensor decomposition and its norm
identity; Chapter IV section 1, Corollary 3, printed p. 64 (PDF p. 81), for
the adelic product; and Chapter IV sections 3-4, printed pp. 71-76
(PDF pp. 88-93), for the idele topology and principal quotient. These
passages were read. Registered original: `weil-1973-basic-number-theory`,
SHA256 `32fff78f8ccc5d6378907941e26746c34e20fc3adf5096508844cfe8a301e33b`.
The quotient and continuity arguments above describe the implemented Lean
proof. This is a conditional reduction of the remaining arithmetic obligation,
not an assumption that the source's full theorem has been formalized.
