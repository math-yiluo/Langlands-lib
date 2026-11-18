# Forced frame maps for identity and composition of framed base extension

This internal unit proves the residue-map coherence needed for actual framed
identity and composition comparisons. `Nilp.reducedScalarMap_id` and
`reducedScalarMap_comp` follow the actual quotient functor identity and
composition laws and the definition of the induced scalar algebra map.

`baseChange_id_residueMap` and `baseChange_comp_residueMap` apply those equations
to the stored residue map of the actual extended representative.
`baseChangeIdentityFrameIso` and `baseChangeCompositionFrameIso` use exactly
the identity-coordinate global-frame isomorphisms forced by the proved
stored-residue equalities. No frame automorphism is selected. Both complete
forward and inverse formal coordinate maps are proved to be the identity;
the inverse equations use the actual integral inverse law.

All local-field, finite-dimensional central-division, embedded-field,
coefficient/residue and height-certified fixed-frame hypotheses remain explicit,
with Nilp universes `{v,u}` for framed objects. The generic induced quotient
scalar-map equations allow Nilp universes `{v,w}`. These are actual integral
fixed-frame isomorphisms and residue equations. Original framed identity and
composition comparisons, class functor laws and representability remain
further obligations.
