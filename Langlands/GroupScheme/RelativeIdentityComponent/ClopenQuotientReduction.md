# Clopen subgroup quotients from separated etale space schemehood

`clopenQuotient_of_separatedEtaleScheme` reduces the unchanged published
`ClopenQuotientStatement` to the general proposition
`AlgebraicSpace.SeparatedEtaleSchemeStatement`. That proposition remains
an explicit premise. This module does not prove the final unconditional
quotient theorem.

The internal theorem
`ClopenQuotient.nonempty_quotient_of_separatedEtaleScheme` works for a
smooth quasi-compact group over any scheme, and any smooth subgroup
whose inclusion is both open and closed. It does not require the
ambient group to be affine or the base to be Noetherian. It applies
the published canonical smooth relation quotient to the actual
right-coset arrow scheme `G ×ₛ H`. The resulting algebraic space has
a smooth surjective projection from `G` and that actual arrow scheme
as its full kernel pair.

The coset inclusion is the base change of the subgroup inclusion along
the right-difference morphism. It is therefore open and closed.
`pairIso` compares the chosen Cartesian product used for group objects
with the categorical binary product used for presheaf diagonals.
The smooth-presentation diagonal theorem descends both immersion
properties to the quotient diagonal. In particular the space is
separated. Since the presenting group is smooth over the base and the
diagonal is open, the structural-atlas theorem gives a scheme atlas
whose map to the base is etale.

The supplied general schemehood proposition now gives an actual scheme
representing the quotient. Its isomorphism with the quotient presheaf
turns the canonical projection into an actual scheme map, and transfers
the smoothness and surjectivity of that map. Closedness of the space
diagonal proves separatedness of the representing scheme. Local finite
presentation descends from `G → S` along the smooth surjective
projection. Quasi-compactness over the base follows by expressing the
preimage of each quasi-compact open of the base as the surjective
continuous image of its preimage in `G`. Quasi-compactness of the
projection follows from quasi-compactness of its composite and
separatedness of the quotient over the base.

The represented kernel-pair square transfers across the representing
isomorphism and the fully faithful scheme Yoneda functor. The published
`HomogeneousCosetRelation.fibers_of_isPullback` then supplies exactly
the required equivalence, on every scheme test, between equality of
quotient images and factorization of the right difference through the
subgroup. No pointwise surjectivity on sections is assumed.

For the target relative identity component, openness is part of its
published representation predicate. Its source group is smooth by
composition with the smooth ambient group. The internal construction
therefore supplies every field of the unchanged
`HomogeneousQuotient` structure, conditionally only on the stated general
schemehood theorem.

Provenance: internal composition of the published actual coset relation,
canonical smooth algebraic-space quotient, scheme-representability
transport and source descent, together with the paired
`SmoothPresentationDiagonal` helper. This is the schemehood reduction in
the representability step of Conrad's Proposition 3.1.3, rather than an
independent assumption of that representability conclusion.
