# Exact diagonalizable quotients over an arbitrary scheme

This is an internal construction derived from the Library's relative
diagonalizable model, explicit exact diagonalizable quotient, and base-change
theorems for subgroup ranges and actual fppf quotients.

For any scheme `S` and homomorphism `p : Λ →+ Γ` of abelian groups,
`diagonalizableMap S p` is the restriction map `D_S(Γ) → D_S(Λ)`.
`diagonalizableExactQuotientMap S p` restricts a character of `Λ` to `ker p`,
giving `D_S(Λ) → D_S(ker p)`. Both definitions are the base changes from
the explicit integral diagonalizable group maps.

If `p` is surjective, its restriction map gives a closed subgroup inclusion.
If also `Λ` is finitely generated, the exact quotient map is the actual fppf
quotient by that subgroup, with equality of the full kernel subgroup functor.
The quotient map is affine, and its target is of multiplicative type.
There is no nonemptiness, reducedness, or Noetherian assumption on `S`.

The proof establishes the fppf quotient over the Noetherian nonzero ring
`ULift ℤ` and uses stability under arbitrary base change. The equality of
subgroup ranges under base change identifies the specified subgroup.
Affineness and the closed inclusion also come from the integral maps by
base change. Finite generation of `ker p` follows by viewing the subgroup
as a submodule of the finite ℤ-module `Λ`. This gives the finitely generated
character presentation used to prove multiplicative type of the quotient.

This module treats inclusions induced by a supplied constant character
surjection. It makes no claim that every map between diagonalizable groups
over a disconnected scheme is given by one such surjection.
