# Gallagher determinant transfer for actual induction

Worker 1767 proves
`Langlands.LocalFactor.Inductive.gallagherDeterminant`, whose complete type is
`Langlands.LocalFactor.Inductive.GallagherDeterminantStatement.{uK,uG,uV}`.
The theorem imports the existing statement without changing its Lean/Markdown
pair or any imported pair.

For every field `K`, group `G`, finite-index subgroup `H`, and actual
finite-dimensional `K`-representation `A` of `H`, the result is

`det(Ind A) = det(Ind 1_H)^rank(A) * transfer(det A)`.

Both determinants are the Library's actual unit-valued determinant characters.
Induction is the existing `FiniteRepresentation.induce` on Mathlib's equivariant
function space, and transfer is the existing `MonoidHom.transfer`. The field,
group, and representation carrier retain their independent universes. There is
no finite-group, normality, characteristic, chosen-basis, splitting,
irreducibility, or semisimplicity premise. Dimension zero is included.

## Implemented proof

All auxiliary declarations are in the namespace
`Langlands.LocalFactor.Inductive.Gallagher`.

For a finite set `I` and finite-dimensional space `V`, `scalarCoordinates` writes
each value of `I → V` in `Module.finBasis K V`, then transposes the two function
indices. Conjugating precomposition by a permutation `p : I ≃ I` through these
coordinates gives one scalar precomposition map on `I → K` for each basis
coordinate. `LinearMap.det_conj` and `LinearMap.det_pi` therefore prove
`det_funLeft`: the determinant on `I → V` is the scalar determinant raised to
`finrank K V`. The basis is chosen internally from finite dimensionality. If the
rank is zero, the determinant product is empty and equals one.

For `x : G`, `inverseCoset H x` is the left coset of `x⁻¹` and
`leftFactor H x` is the subgroup element
`x * representative(inverseCoset H x)`. Its membership in `H` follows from
quotient equality. The lemmas `inverseCoset_mul` and `leftFactor_mul` show their
compatibility with left multiplication by `H`.

`leftCoordinates H A` evaluates an actual equivariant function `f` at `t(q)⁻¹`,
where `q : G/H` and `t(q) = q.out`. Its inverse sends a tuple `v` to
`x ↦ A(leftFactor H x)(v(inverseCoset H x))`. The proof verifies equivariance,
both inverse laws, and linearity. These are auxiliary coordinates on the existing
induction construction; no replacement induced representation is introduced.

In these coordinates, right translation by `g` is

`v(q) ↦ A(s(q,g))(v(g⁻¹ • q))`,

where `s(q,g) = t(q)⁻¹ * g * t(g⁻¹ • q)` belongs to `H`. This is a block action
composed with the precomposition permutation `q ↦ g⁻¹ • q`.
`det_induce` applies determinant multiplicativity, `LinearMap.det_pi`, and
`det_funLeft` to obtain the scalar permutation determinant raised to `A.rank`,
multiplied by the product of the determinants of `A(s(q,g))`.
For the trivial scalar representation every block is the identity and its rank
is one. Thus `det_induce_trivial` identifies the scalar permutation determinant
with the determinant of the actual induced trivial line.

`transfer_leftFactors` unfolds `MonoidHom.transfer_def` using the default left
transversal, whose representatives are `q.out`. The translated transversal's
representative is `g * t(g⁻¹ • q)`, so the defining product is exactly
`∏ q, φ(s(q,g))` for `φ : H →* Kˣ`. This verifies the transfer convention directly,
including the inverse in the coset permutation. Finally, equality of characters
is checked at each `g` and then in the field after coercion from units;
`Units.coe_prod` and `determinantCharacter_apply` identify the remaining product.

## Source and provenance

The target is Deligne, *Les constantes des équations fonctionnelles des
fonctions L* (1973), Proposition 1.2 (Gallagher), printed p.508, retained PDF p.8.
Section 1.1, printed p.507/PDF p.7, supplies the arbitrary-field, arbitrary-group,
finite-index conventions. Source ID `deligne-1973-local-constants`, SHA-256
`b03f483c4eeca79b75e34b88f41406fe4c9e16ba621480ce859697c93e8d5844`.
Both pages were read directly. Deligne states the virtual dimension-zero formula
and the general correction by the determinant of the permutation representation.
The present theorem proves precisely the existing actual-representation target;
it does not construct a virtual-representation descent.

The proof above is an internal algebraic derivation, rather than Deligne's
classifying-space explanation. The new coordinate equivalences and intermediate
lemmas are justified by their explicit inverse laws and determinant calculations.
It reuses the published statement, actual induction and determinant constructions,
and pinned Mathlib's quotient, transfer and determinant lemmas through imports.

## Validation

The complete proof module is checked in environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`). Compilation and declaration inspection
are development checks; independent semantic review and publication remain
separate requirements.
