# The formal division summand of a split order action

Rapoport–Zink, *Period Spaces for p-divisible Groups* (1996), §6.43 and (6.17), printed pp. 308–309 (PDF pp. 320–321), describe the polarized split pair using the two factors of the order. The primal summand in the convention of `SplitOrderTangent` is the one with the ordinary division order action.

`OrderAction.divisionProjector` acts by the actual order element \((0,1)\). `OrderAction.DivisionImage` presents its image in formal coordinates. `DivisionImage.order` restricts \((0,b)\) along the inclusion and projection to give the action of \(b\) on the image law. The product formula for restricted morphisms proves multiplicativity. On that law the projector acts as the identity, and the restricted central action is the given scalar action.

At any coefficient ring point, the derivative of inclusion gives `DivisionImage.tangentEquiv`, with inverse obtained by differentiating the projection. It identifies the tangent of the presented law with the image of the actual tangent projector and intertwines the division order actions. Thus the tangent used by the split special condition can be computed on the presented summand.
