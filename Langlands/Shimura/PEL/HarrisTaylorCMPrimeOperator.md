# The actual prime Tate operator of a fixed Harris self-isogeny

This internal unit uses the actual rational prime Hom map to construct
`selfIsoPrimeTateOperator` for a rational automorphism of the action object
underlying a positive polarized Harris CM object. Its prime is the rational
prime associated to the specified finite place, and its values are endomorphisms
of the actual p-adic rational Tate module at the given field-valued point.

`selfIsoPrimeTateOperator_eq_id_of_levelIso_fixed` retains the original
geometric prerequisites, a fixed orbit at an original Harris level, local
smallness at that finite place, and finite order of the actual rational
endomorphism underlying the self-isogeny. The earlier Harris local comparison
makes prime extraction fixed for every full rational Tate section. The actual
prime extraction is surjective and natural for rational Hom, by
`rationalHomMap_eq_id_of_extraction_fixed`; applying that result proves identity
of the actual prime Tate operator.

The finite-order premise is explicit. This consequence supplies no proof of
that premise, positivity, or injectivity of the rational Hom representation at
one prime. It therefore does not identify the self-isogeny itself or prove
`CMSmallLevelRigidityStatement`. All constructions and identities in this unit
are consequences of the imported actual maps; no external source result is
asserted here.
