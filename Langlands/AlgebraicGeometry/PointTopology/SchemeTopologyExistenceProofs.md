# The canonical scheme-point topology satisfies the source axioms

Author: Worker 105.

The entry theorem `schemePointTopologyExistence_proof` proves exactly the
published proposition `SchemePointTopologyExistenceProperty R S`. Its coefficient
ring and local value algebra are arbitrary commutative rings in a common
arbitrary universe. Only the value algebra `S` is topologized; it has
`IsTopologicalRing S`, `IsLocalRing S` and `IsOpenUnits S`. The topology is exactly
`evaluationSchemePointTopologyFamily R S`, on actual relative scheme morphisms.
No Hausdorffness, separatedness, compactness or finite presentation is required.

The implementation reuses the published continuity, pullback and closed-immersion
proofs directly. For open immersions, `schemePointIsoHomeomorph` first turns an
actual relative isomorphism into a point homeomorphism: its maps are actual
postcomposition by the isomorphism and its inverse, and both are continuous by
the general scheme-point continuity theorem. An arbitrary open immersion is
identified with the open subscheme defined by its actual scheme image using
Mathlib's equal-range isomorphism. The relative structure equation follows from
the immersion's original base equation. Composition of this point homeomorphism
with the published open-subscheme point open embedding proves
`isOpenEmbedding_schemePointMap`, for arbitrary relative schemes.

The final theorem applies the first three published clauses, the just-proved
arbitrary-open-immersion clause, and the affine-line normalization. For the last
clause it rewrites the final point topology of the actual affine line to the
affine evaluation topology using `schemePointTopology_eq_affine`, then uses the
published affine existence theorem. All maps are the named actual point maps;
no assumed topology package replaces any conclusion.

The source motivation is Conrad Proposition 3.1, printed page 4, as qualified in
the target Markdown. This is its existence clause in the derived relative
formulation with separate coefficient and value rings. Uniqueness and the
Hausdorff and local-compactness consequences remain separate proof units, and
this result does not complete the remaining sections of the paper.
