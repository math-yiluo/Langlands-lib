# Descent of models stabilizing a Galois-stable building subset

This is an internal consequence of the published semilinear building action and
the smooth-model descent interface. It is conditional on
`UnramifiedSmoothModelDescentStatement` and on a supplied smooth model over the
maximal unramified integers whose actual integral-point image is the setwise
stabilizer of a supplied subset. It proves neither of those inputs. All
constructions and lemmas hold in arbitrary universe `u`.

For arbitrary supplied building data `C` and semilinear apartment data `D`,
`SemilinearApartmentData.conjugate_stabilizes` proves that coefficient
conjugation preserves the setwise stabilizer of every subset `Y` satisfying
`D.action σ '' Y = Y` for each coefficient automorphism. The calculation uses
`D.action_smul` to interchange the coefficient action with the original
rational-point action. Applying it to a stabilizer element and using the two
image equalities gives the desired image equality for its conjugate. There is
no chamber, boundedness, simple-connectedness or apartment-uniqueness input to
this calculation.

`stableSetModel_galois_stable` transfers this calculation through the supplied
equivalence between model-point membership and setwise stabilization. It
establishes exactly the Galois-stability premise of smooth model descent.
`exists_descendedStableSetModel` then applies that supplied descent statement,
and `descendedStableSetModel` chooses its smooth integral model over the original
local integers. The accompanying lemmas retain smoothness and the actual model
isomorphism over the identity of the generic group.

Finally, `descendedStableSetModel_mem_integralPoints_iff` uses that isomorphism's
`integralPoints_eq` theorem to identify the unramified integral-point image of
the chosen descent with the original supplied model's image, hence with the
setwise stabilizer of `Y`. This file asserts no connectedness of special fibres;
that consequence is supplied separately by the connected-fibre descent helper.
