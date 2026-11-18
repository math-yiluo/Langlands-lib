# Actual composition coherence of the Nilp quotient-square maps

`reductionCompositionScalarIso` constructs the actual full-order atlas
coefficient-composition isomorphism on the quotient base. It follows the
specified comparison for the two induced quotient scalar maps by the
identity-coordinate equality correction forced by the quotient functor's
composition law. Its target is extension along the quotient scalar map of the
actual composite Nilp morphism.

`reductionBaseChange_comp` is an equality of whole actual integral full-order
atlas isomorphisms. Its first route follows the second quotient/base-change
square, extends the first quotient/base-change square along the second quotient
scalar map, then uses the corrected quotient coefficient-composition map.
Its second route reduces the original coefficient-composition isomorphism,
then follows the quotient/base-change square of the composite Nilp map.
All maps and corrections are the specified existing actual constructions.

The proof specializes `baseAlongSquareIso_comp` to the actual three quotient
maps and the two quotient scalar maps, using the proved quotient naturality
equalities. The quotient functor's composition equality supplies the final
scalar correction. The auxiliary `baseAlongSquareIso_target_eq` identifies
that corrected outer square with the specified square of the composite map by
equality elimination. Integral associativity pastes these equations.

The coefficient ring and acting ring retain separate universes, with an
arbitrary finite coordinate type. Nilp reduction uses universes {v,w}. No
domain or rational-field hypothesis is required. Covers may be infinite and
coefficient maps may merge principal generators. This is internal coherence of
the existing actual quotient/base-change maps; the original framed composition
comparison and quotient composition law remain subsequent constructions.
