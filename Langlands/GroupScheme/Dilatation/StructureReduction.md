# From the special fibre to the structural conclusions

`dilatation_structure_of_specialFibre` takes a smooth, geometrically connected morphism from the special fibre of the dilatation to the smooth centre. Composing with the structure map of the centre gives smoothness of the special fibre. The generic identification carries smoothness from the original model to the generic fibre of the dilatation. The smooth-fibre criterion over the discrete valuation ring then gives smoothness of the dilatation.

If the centre is geometrically connected, composition gives geometric connectedness of the special fibre. `hasGeometricallyConnectedFibres_of_generic_special` compares the genuine scheme fibres over the generic and closed points with the supplied fraction-field and residue-field models. Those are the two points of the base, so a geometrically connected generic group gives geometric connectedness of all the fibres.

`smoothCongruenceModels_of_smoothDilatation` dilates at the unit section of the current special fibre. The centre is the residue-field spectrum and is smooth and geometrically connected. The first positive level is that dilatation, and induction uses the compatible addition isomorphism to identify each subsequent level. This is the iteration of Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*, Appendix A.5.12–14, printed pp. 636–637.
