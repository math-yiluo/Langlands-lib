# Affine slices from transverse differential equations

This private draft combines the algebraic differential slicing proof with
affine quotient pullbacks and the scheme etale locus.

`exists_ideal_etale_quotient_of_residue_span` assumes that the differentials
of elements pulled back from an ideal `p` of `A` span the residue cotangent
fiber at a prime of the smooth `A`-algebra `B`. The pullback map `θ` may
differ from the smooth algebra structure. It selects finitely many allowed
equations using the differential slicing lemma, chooses their preimages in
`p`, and forms their finitely generated ideal `I`. After a principal
localization outside the prime, the quotient by the extended ideal is
etale over `A` for the original smooth algebra structure. The proof uses
the image-of-span identity to identify the ideal of selected equations.

These are internal constructions. No good-point existence, relation
propagation or global slicing assertion is proved here.

`exists_affineSlice_formallyEtale_of_residue_span` applies the equation choice
and the localized quotient pullback construction. In addition to the residue
spanning input, it assumes `p` is contained in the inverse image under `θ` of
the chosen prime. It returns a finitely generated ideal `I ≤ p` and a point
of the full pullback `Spec(A/I) × Spec B` above that prime where the stalk of
the second projection followed by the original smooth map is formally etale.
The prime-avoidance and containment hypotheses lift the point through the
principal localization and quotient. Cancelling the open immersion on stalks
transfers etaleness to the full pullback. This remains an affine construction;
no good-point or global surjectivity assertion is supplied.
