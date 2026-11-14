# Integral translates into a dynamic opposite cell

This internal construction combines the fixed quotient reflection cell,
exact Henselian lifting of character-negating normalizers and lifting of
opposite-cell coordinates from a special-fibre quotient. It works at arbitrary
universe `u`.

The base is a Henselian local domain with perfect residue field and a supplied
fraction field. The ambient integral model is smooth, affine and of finite type,
and its special fibre is connected. An integral split torus maps to this model.
An integral character pairs strictly positively with an integral cocharacter.
The original character need not be a root.

The supplied actual special-fibre map `q` is smooth and surjective onto an affine
connected reductive quotient. Its full scheme-theoretic kernel is connected
and unipotent. The integral torus's special fibre maps monomorphically onto a
maximal split torus of that quotient. Quotient conjugation actually descends
through the residue of the original character to an automorphic action of
the multiplicative group. The quotient positive dynamic subgroup is nontrivial.
These geometric conditions remain explicit; the construction does not derive
them for a particular integral model.

`Dynamic.oppositeCocharacter_torus` identifies the opposite dynamic cocharacter
of a torus cocharacter with its negative in the actual cocharacter lattice.
It uses inversion on the multiplicative group and additivity of composition.

`henselianReflectionCellLift` chooses one integral section `m` and one actual
integral torus automorphism, with the normalizing equation and negation of the
original integral character. For every integral section `x` whose quotient
reduction is a nonidentity point of the positive dynamic subgroup, it supplies
actual integral coordinates of `x * m⁻¹` in the opposite-unipotent/parabolic cell.
Both factors use the canonical affine dynamic representatives over the
integral base.

The proof first applies `dynamicReflectionCellNormalizerLift` to the full
scheme kernel of `q`. Smoothness makes this an actual fppf quotient with a
smooth kernel. It then applies `henselianRootNormalizerLift` to that exact
residue normalizer and torus automorphism, retaining the residue point.
Reduction of `x * m⁻¹` is therefore the quotient point in the previously
constructed ordinary dynamic cell. Representability turns its two functor
memberships into actual quotient coordinates.
`oppositeCell_section_lifts_iff_quotient_reduction` lifts those coordinates
to integral coordinates of the translated section.

This is a composition of the named internal Library constructions, without
an additional original-literature assertion. It does not identify the generic
normalizer with a root reflection or assert integrality of prescribed opposite
factors. The final fixed-point theorem remains outside this unit's scope.
