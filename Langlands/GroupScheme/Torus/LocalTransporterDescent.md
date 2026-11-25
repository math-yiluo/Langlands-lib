# Zariski local transporter descent

Internal derivation from the published split torus cocycle trivializations,
local coset descent, and transporter identities. For any base scheme, transporters for
two maps from a commutative split torus descend Zariski locally from an affine flat
surjective cover when the second map is monomorphic and its full centralizer equals
its actual range. Their inverse differences give the torus cocycle. Local coset descent
corrects the cover point by a torus point. That correction preserves the transporter
condition, which descends by epimorphic cancellation after pulling back each test
scheme along the cover. All relations hold on arbitrary schemes, including nilpotents.

`LocalTransporterData i₁ i₂ s` stores an open neighbourhood of `s`, a point of
the ambient group over that open, and its all-test transporter equation.
`localTransporterOfCover` chooses such data using
`exists_local_transporter_of_cover`. This choice construction adds no
canonicity or uniqueness claim.
