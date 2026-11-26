# Real cuspidal restriction from local Whittaker range comparison

`RealPlaceWhittakerRestrictionFromNormalizedRangeStatement` derives the full real restriction implication for both characters from `RealWhittakerNormalizedRangeStatement`. The local premise asks that the range of any normalized Whittaker intertwiner of the specified irreducible real standard module contain the ordinary coefficient model. It applies to groups of size at least two.

The actual-place intertwiner theorem gives a linear map into the cuspidal realization and a normalized Whittaker map whose coefficients are the restrictions of its image vectors. The local range inclusion gives a preimage for each required coefficient in the standard module. Its image in the cuspidal realization gives the desired restriction with finite coordinate one. The same construction with the inverse adelic character uses its local scale `-a`.

`realPlaceWhittakerRestriction_rankOne` gives both implications for `GL₁`, where the total rank condition gives a single character block. The rank-one model calculation writes every coefficient as a scalar multiple of that character composed with determinant. The normalized coefficient is the character itself, so linearity supplies the same preimage argument in rank one. In higher ranks, irreducibility of the real standard module comes from the irreducibility theorem for supplied parameters of cuspidal realizations.

This is an internal consequence of the actual-place intertwiner theorem and the rank-one model calculation. The local premise concerns the ordinary algebraic coefficient model, with a polynomial exponent allowed to depend on the source vector.
