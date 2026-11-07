# The determinant-band form on the original operator realization

This is an internal construction from the existing operator realization,
continuous rational quotient, determinant-slice geometry and Mathlib L2 inner
product. It does not claim the final cuspidal local-unitarity theorem.

For an arbitrary-universe number field and rank `n`, `point` represents an actual
adelic matrix in the principal rational quotient and is surjective. `translate`
is the quotient homeomorphism sending `[x]` to `[x*g]`. The representative
identities retain the original determinant norm and the exact evaluation of
`OperatorRealization.toContinuous`. `toQuotient_finite` identifies the original
finite adelic representation with this positive right translation.
`toQuotient_central` records the original common scalar-idele character on the
same quotient function, using commutativity of scalar matrices.

Given a measure on this quotient and square integrability of every original
vector on the open determinant band `(1,2)`, `toL2` is the linear map to L2 of
the restricted measure. `inner_toL2` identifies its inner product with the
integral of the original pointwise Hermitian product. It uses the almost
everywhere representatives supplied by `MemLp.toLp`.

For `n != 0`, a central character and full support of the quotient measure,
`toL2_injective` proves faithfulness. A vector mapping to zero vanishes almost
everywhere on the band. Continuity and positivity on open sets upgrade this to
pointwise vanishing there. A scalar idele carries any adelic matrix into the
band by prescribing its resulting determinant norm to be `3/2`. The central
character has nonzero values, so its evaluation identity forces the original
vector to vanish everywhere. The already faithful quotient-function map then
forces the vector itself to be zero. This argument needs neither a unitary
character nor finite band volume.

`measurePreserving_translate_band` restricts a supplied measure-preserving
norm-one translation to the band. For a unitary central character,
`inner_toL2_finite` proves invariance under every original finite adelic action.
It corrects that translation by a scalar idele so that its determinant norm is
one. The common scalar character contributes a phase of norm one, which cancels
from the pointwise Hermitian product (`inner_phase`). Change of variables under
the corrected, measure-preserving quotient homeomorphism then gives equality of
the band integrals.

`finiteInvariantPositiveForm` pulls the L2 inner product back to the unchanged
carrier `S.Space` with the unchanged action `S.finiteRepresentation`. Its
Hermitian symmetry, nonnegativity, additivity and conjugate linearity are the
standard L2 identities. Faithfulness proves definiteness, and the preceding
change-of-variables argument proves action invariance. Its premises are positive
rank, a unitary common central character, a full-support quotient measure,
square integrability of every original vector on the band and preservation of
that measure under every determinant-norm-one right translation.

The construction is a focused analytic bridge. It does not prove those measure
or square-integrability premises from cuspidality; they remain obligations of
the final theorem. It assumes no finite band volume and supplies no compact or
differential invariance assertion. All positive ranks, including one, are
retained. There is no presentation-universe parameter in this intermediate
construction.
