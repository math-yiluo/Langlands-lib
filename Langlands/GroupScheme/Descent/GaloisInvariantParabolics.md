# Effective descent of Galois-invariant actual parabolics

Author: Worker 82.

This unit retains actual group schemes, closed inclusions, and the existing
all-test Galois transport `radicalGaloisHom`. It does not replace a subgroup
by its rational points or assume an already descended subgroup.

`IsParabolicSubgroup.of_baseChange_of_algebraicExtension` reflects
parabolicity along any algebraic field extension `L/F`, given the original
closed inclusion. Smoothness of the original source follows by faithfully
flat descent from its upper-field smoothness. The two chosen algebraic
closures are isomorphic over `F`: the published closure embedding is
surjective because the target is algebraic over an algebraically closed
field. The proof transports the actual geometric Borel witness from the
upper-field parabolic through the canonical iterated-base-change
comparison, then pulls it back along the inverse closure isomorphism.
Naturality gives its exact factorization through the original inclusion.
These are precisely the smoothness and geometric Borel clauses of the
existing parabolic predicate.

`Descent.ParabolicGaloisDescentData p` contains an actual affine group
scheme over `F`, its parabolic inclusion into the original ambient group,
an isomorphism of its base change with the specified upper-field source,
and the exact recovery equation for the original inclusion `p`.

For any Galois extension and any actual parabolic whose all-test image is
preserved by every `radicalGaloisHom p σ`, the proved closed-subgroup
descent theorem constructs the ground-field inclusion and recovery
isomorphism. The original upper-field parabolic property transfers to
the base change of that inclusion. The reflection theorem just proved
therefore supplies its ground-field parabolic property.
`nonempty_parabolicGaloisDescentData` proves existence, and
`parabolicGaloisDescent` selects such actual data. The extension need
not have finite degree. The ambient group must be affine; no
connectedness, reductivity or compactness premise is added to this
descent construction.

`IsMaximalSplitTorus.isIso_parabolic_of_galoisInvariant` adds connected
reductivity and a central maximal split torus in the ground-field
ambient group. The constructed ground-field parabolic inclusion is an
isomorphism by `CentralMaximalSplitParabolic`. Its base change and the
exact recovery equation show that the original upper-field inclusion
is an isomorphism as well. Thus a proper upper-field parabolic cannot
have this all-test Galois invariance under the stated centrality
hypothesis.

This is internal derived infrastructure for the Galois-stable
proper-parabolic step in Springer, *Reduction theory over global fields*
(1994), §3.5, printed p.215 (PDF p.9). The implementation uses published
effective affine closed-subgroup descent and actual geometric Borel
comparisons, rather than an unproved descent assertion.
The registered source is `springer-1994-reduction-global-fields`,
SHA-256 `774f5531200db07140b30ffb8f4adce8cf3a3914ca9f38b796f2a2d24ff18496`,
file `literature/Reduction theory over global fields (Springer, 1994).pdf`.
No errata note exists. This unit constructs no Galois-invariant
parabolic from root estimates, proves no Weyl overlap estimate or
uniform root lower bound, and proves no adelic compactness theorem.
