# Arbitrary diagonalizable scheme actions

This module uses the actual point-law action and all-refinement fixedness from
[PointwiseSchemeAction](../PointwiseSchemeAction.md).

For a diagonalizable acting group `D(M)` and a target which is an affine group
scheme `G` as a scheme, `CharacterAction.ofPointwiseSchemeAction` transports the action
to algebra-valued points of `AffineCoordinates.algebra G`. The group law on
`G` supplies its already chosen coordinates; preservation of that law by the
action is not assumed. `pointEquiv_schemeAct` states compatibility with the
original scheme action. `isFixed_iff_schemeAction` uses the preceding affine
refinement comparison and the diagonalizable character-point equivalence to
identify its coordinate fixedness with actual all-scheme fixedness.

`schemeActionFixedIdeal` is the coefficient ideal from the resulting natural
character action. The algebraic kernel criterion gives
`schemeActionFixedIdeal_le_ker_iff`: an algebra point kills this ideal exactly
when the corresponding actual scheme point is fixed after every scheme
refinement. Finally, `formallySmooth_schemeActionFixedQuotient` applies the
homogeneous-coaction fixed-quotient theorem. It assumes precisely formal
smoothness of the chosen coordinate algebra over `R`. There is no field,
characteristic, finite generation, or torsion-free hypothesis on `R` or `M`.

The provenance is internal: this generalizes the adapter in
`AffineCharacterAction`, following the same proof with only identity,
associativity and naturality. The intended application is lifting points in
twisted transporters, but this module does not construct a twisted action or
assert a geometric smooth representative, connectedness, dynamic subgroup
properties, or a Lie-image comparison. Milne, *Algebraic Groups* (2017),
Theorem 13.1 and Corollary 13.10, printed pp.254–257 / PDF pp.270–273, provide
context for fixed-locus smoothness. The retained official corrections to the
proofs of 13.4 and 13.5 concern the local-ring route, whereas the imported
algebraic theorem uses a square-zero lifting proof. Worker 1131's contribution
to that reused algebraic argument is credited in the submission.
