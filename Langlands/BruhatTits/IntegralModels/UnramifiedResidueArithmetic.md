# The induced residue algebra of the maximal unramified extension

This internal provider relocates the three published lemmas
`unramifiedResidueAlgebra_eq`, `unramifiedResidue_isAlgebraic` and
`unramifiedResidue_isSeparable` from `UnramifiedFacetSignDescent`, preserving
their names, types and proof bodies. The original module imports this provider.
The local integer algebra, scalar tower and local homomorphism use the same
published `Valuation.HasExtension` constructions, with distinct local names.
No new literature assertion is added.

For a nonarchimedean local field `F` in arbitrary universe `u`, let
`K = inertiaFixedField F` and `O = fixedFieldIntegers F`. The residue algebra
induced by the actual integer-ring extension `𝒪[F] → O` agrees with
`(residueToFixedField F).toAlgebra`. Consequently this induced residue-field
extension is algebraic and separable. The proposition
`UnramifiedResidueArithmeticStatement` records the conjunction of these last
two conclusions. There is no characteristic restriction.

The equality proof checks algebra maps on residues of integers, using
surjectivity of the residue map and definitional equality. Algebraicity is the
algebraicity clause of the published `fixedFieldResidueIsAlgClosure`, transported
along that equality of algebra structures. Separability follows because the
residue field of `F` is finite and hence perfect. The final theorem pairs the
two unchanged arithmetic lemmas.

`UnramifiedRecoveredRootRestriction` now imports this provider directly for
validity of its actual recovered reductive quotient. Its declarations and
proof bodies are unchanged. This records the arithmetic dependency without
using the unrelated facet-sign descent module.
