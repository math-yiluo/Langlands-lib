# Actual upper Bruhat cells and elementary coordinate maps

Author: Worker 176.

This pair constructs the actual upper triangular double coset and its subtype,
the lower unipotent group and the plus and minus permutation subgroups.
It also constructs the two multiplication maps appearing in Shalika (1974),
printed pp.175–176. The subgroup convention is exactly the formula on printed
p.174: `U_w⁺ = U ∩ w⁻¹ U w` and `U_w⁻ = U ∩ w⁻¹ Ubar w`.

The registered original is `shalika-1974-multiplicity-one`, J. A. Shalika,
*The multiplicity one theorem for GLn*, Ann. of Math. (2) 100 (1974),
171–193. The original retained at
`/home/taskhub/central-library/Shalika--The multiplicity one theorem for GLn--1974.pdf`
has SHA256 `788c5d124024c768aa47c4e8b179475fbcf5b0882a518ae60b19cdc88089f087`.
Printed pp.174–176 (one-based PDF pages 5–7) were read and visually checked.
No matching source-specific errata was found.

Page-index clarification (added by Worker 755; the reading assertion above
is Worker 176's). In this exact PDF, printed p.174 is zero-based page index 4
and one-based PDF page 5; printed pp.175 and 176 are zero-based indices 5
and 6, that is one-based pages 6 and 7. Zero-based indices are those of
`pypdf.PdfReader(...).pages[i]`; one-based pages are those of a PDF viewer
and of the `resource_pdf` `page` argument. The one-based locator above is
therefore correct as stated. This was rechecked against the SHA256 above,
in agreement with the earlier independent checks by Worker 16 and Worker 634.

All declarations below are in `Langlands.GeneralLinear`. The cell and subgroup
constructions are over every commutative ring `R` in an arbitrary universe and
every natural rank `n`, including zero. No positivity or nontriviality hypothesis
is imposed. The torus map uses the published field-general
`Iwasawa.diagonalUnits` for a field `K`, with no valuation input. The inherited
topology is the existing topology on units of matrices, followed by subgroup
and cell subtype topologies. Products and `Fin n → Kˣ` carry their standard
product and function-space topologies. Continuity of multiplication assumes
`TopologicalSpace R` and `IsTopologicalRing R` (or the corresponding instances
for `K`). In particular the declarations specialize to a field with its
canonical p-adic topology whenever these standard instances are present.

The permutation convention sends `e_j` to `e_(w j)`. Its conjugation law
has entry `g (w⁻¹ i) (w⁻¹ j)`. Consequently the extra vanishing conditions
are `w j < w i` for plus and `w i < w j` for minus. These conditions and
the trivial intersection are proved, rather than assumed.

The following table identifies the principal constructions and their source
correspondence. Here `p = permutation n R w`, `B = upperTriangularSubgroup n R`
and `U = upperUnipotent n R`, all imported without modification.

| Lean name | Meaning and source |
| --- | --- |
| `upperBruhatCell` | The actual set `{g | ∃ b₁ ∈ B, ∃ b₂ ∈ B, g = b₁ * p * b₂}`, corresponding to Shalika's upper Bruhat cell `BwB` on printed pp.174–175. |
| `UpperBruhatCell` | The subtype of that set, using the ordinary subtype topology; an internal packaging of the source's cell. |
| `lowerUnipotent` | The inverse image of `U` under conjugation by the existing `weylLong n R`; this implements the source's opposite unipotent group `Ubar`. Its lower-entry description is proved below. |
| `permutationUnipotentPlus` | `U ∩ {g | p*g*p⁻¹ ∈ U}`, exactly `U ∩ w⁻¹ U w` from printed p.174. |
| `permutationUnipotentMinus` | `U ∩ {g | p*g*p⁻¹ ∈ Ubar}`, exactly `U ∩ w⁻¹ Ubar w` from printed p.174. |
| `upperBruhatCellMap` | `B × U_w⁻ → UpperBruhatCell n R w`, `(b,v) ↦ b*p*v`, the map on printed p.175, where the source writes the first argument as `hu`. |
| `upperBruhatTorusMap` | `U × (Fin n → Kˣ) × U → UpperBruhatCell n K w`, `(u₁,d,u₂) ↦ u₁*p*Iwasawa.diagonalUnits d*u₂`, the multiplication map on printed p.176. Lean's product is right-associated. |

The commutative-ring generality, subtype packaging, action instances, entry
lemmas and elementary proofs are internal deductions from the imported actual
matrix-group APIs. They do not invoke the later conclusions of Shalika's
argument.

`mem_upperBruhatCell_iff` exposes the defining existential formula.
`mul_mem_upperBruhatCell` and `mem_upperBruhatCell_mul` prove stability under
left and right multiplication by `B`, by multiplying the appropriate witness
and using associativity. The instances `upperBruhatCellLeftAction` and
`upperBruhatCellRightAction` supply these actions. The right action uses
`Bᵐᵒᵖ`, so its operation is actual right multiplication in the correct order.
`upperUnipotentInUpperTriangular` is the subgroup inclusion obtained from
`upperUnipotent_le_upperTriangular`. The instances
`upperBruhatCellUnipotentLeftAction` and
`upperBruhatCellUnipotentRightAction` restrict the two actions through this
inclusion and its opposite. The four `upperBruhatCell_*_smul_val` lemmas expose
the underlying products.

`mem_upperUnipotent_iff` restates the imported condition: the entries below
the diagonal vanish and all diagonal entries are one.
`mem_lowerUnipotent_iff` proves the corresponding lower condition: the entries
above the diagonal vanish and all diagonal entries are one. Its proof applies
the imported `weylLong_conjugate_entry` and the order-reversing involution
`Fin.rev`. `upperUnipotent_inf_lowerUnipotent` then proves that their intersection
is trivial by matrix extensionality and the three possibilities `i < j`,
`i = j`, and `j < i`.

`mem_permutationUnipotentPlus_iff` and
`mem_permutationUnipotentMinus_iff` expose the conjugation membership formulas.
The respective `*_iff_entries` lemmas prove, using
`permutation_conjugate_entry`, that membership is equivalent to membership in
`U` together with vanishing at every entry satisfying `w j < w i` for plus,
or `w i < w j` for minus. Both directions explicitly transport the indices by
`w` and `w⁻¹`. The lemmas `permutationUnipotentPlus_le_upperUnipotent` and
`permutationUnipotentMinus_le_upperUnipotent` expose the subgroup inclusions.
`permutationUnipotentPlus_inf_minus` sends an element of the intersection by
conjugation into `U ∩ Ubar`, uses the preceding trivial-intersection result,
and uses injectivity of conjugation to recover the identity.

For the first multiplication map, `upperBruhatCellMap_val` is its evaluation
formula and `upperBruhatCellMap_mem` proves membership using `U_w⁻ ≤ U ≤ B`.
`continuous_upperBruhatCellMap` composes the continuous projections and subgroup
inclusions with multiplication by the fixed permutation matrix, then lifts
the result into the subtype.

For the torus map, `diagonalUnits_mem_upperTriangular` checks the off-diagonal
entries of the imported diagonal matrix.
`permutation_mul_diagonalUnits` proves the precise identity
`p * diagonalUnits d = diagonalUnits (fun i => d (w⁻¹ i)) * p`
using the published left- and right-permutation entry formulas.
`unipotent_diagonal_mem_upperBruhatCell` uses this identity to put the diagonal
factor into the left `B` witness. `upperBruhatTorusMap_val` is the evaluation
formula. `continuous_diagonalUnits` checks continuity of both the matrix and its
inverse using the topology on units; it requires only `TopologicalSpace K`.
`continuous_upperBruhatTorusMap` then uses continuous multiplication under
`IsTopologicalRing K` and lifts into the cell subtype. The two bundled maps
`upperBruhatCellMapContinuous` and `upperBruhatTorusMapContinuous` are the same
maps with these continuity proofs.

The two multiplication maps have proved evaluation, membership and continuity
laws. This file does not prove injectivity, surjectivity, uniqueness of
coordinates, Bruhat decomposition, any quotient-map or homeomorphism assertion,
local closedness, boundary dimension, analytic submanifold or dimension results,
or any assertion about distributions or integration. None of these properties
is included as a field or an assumption of a construction.
