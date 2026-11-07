# Local commutator movement into a full-residue field

Let `K` be an actual nonarchimedean local field and `D` a finite-dimensional
central division `K`-algebra, in an arbitrary common universe and without
a characteristic restriction. Let `ι : L →ₐ[K] D` embed a finite field
extension, with an independent universe for `L`. The valuation and
residue maps are the actual reduced-norm valuation on `D` and its
restriction along `ι`.

`localDivision_move_unit` assumes that the induced residue map of `L`
is surjective and that the degree of the actual division residue over
the base residue equals the reduced degree of `D`. For every original
unit `a : Dˣ` of valuation one, it produces `c` in the actual
commutator subgroup of `Dˣ` such that `c * a` lies in the image of
`Lˣ`. These structural premises remain explicit in this helper;
the unconditional local SK1 theorem must supply them.

The proof first works with a unit of the actual integer subring.
Choose a multiplicative generator `z` of the finite division residue
field and a monic integral lift `f` of its minimal polynomial. Its
field polynomial is irreducible. Since `z` also generates the residue
as an algebra, that polynomial has degree equal to the residue degree,
and hence to the reduced degree by the stated hypothesis.

Hensel lifting gives an integral root `b` of `f` inside `L`, reducing
to `z`. Its residue is nonzero, so `b` is an integer-ring unit. Lift
the residue of `a` to an integer-ring unit `a'` of `L`. In the original
integer-unit group form `t = a * ι(a')⁻¹ * ι(b)`. Its residue is again
`z`, so the actual singleton subfield `K(t)` has full residue.
Hensel lifting gives a root of the same `f` in `K(t)`.

The maximal-root equivalence from `DivisionMaximalRootEmbedding`
identifies `K(t)` with the root field of `f`: evaluation is injective,
its source has reduced degree, and the singleton-field degree bound
forces surjectivity. The common root in `L` therefore embeds the whole
field `K(t)` into `L`. Field-embedding conjugacy gives an original unit
`u` with `t = u * ι(y) * u⁻¹` for an actual `y : Lˣ`. The published
movement identity then shows that `[u⁻¹,t] * a` lies in the field-unit
image. This proves `localDivision_move_integerUnit`. Converting a
valuation-one unit into a unit of its actual integer ring proves
`localDivision_move_unit`.

`localDivisionMovementCommutator` chooses the commutator supplied by
this existence theorem. Its specification proves both commutator
subgroup membership and the asserted field-image membership.
`localDivisionSubfield_aeval_base_polynomial` is the elementary
evaluation compatibility used for the two Hensel roots.

This is an internal deduction from the existing actual valuation,
residue generator, scalar polynomial lifting, Hensel lifting,
singleton-field degree bound, field-embedding conjugacy and elementary
unit movement results. It does not assume a conjugating unit or a
movement conclusion. It does not by itself prove the residue-degree
formula, existence of a cyclic subfield, or local SK1.
