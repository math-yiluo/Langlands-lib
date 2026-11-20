# Linear coordinate maps and formal idempotents

A linear map between the coordinate modules is realized by its usual degree-one series with zero constant terms. The tangent of this coordinate map is the original linear map. Substituting one such map into another computes matrix composition.

The construction is internal to the coordinates for the direct summands in the Rapoport–Zink split moduli problem. For a pointed projector \(e\) with tangent \(P\), `CoordinateMap.linearizingMap` sends \(x\) to \(P(e(x))+(1-P)(x-e(x))\) in coefficient coordinates. Its tangent is the identity because \(P\) is idempotent. Both its composite with \(e\) and its postcomposition with the linear projector are \(P(e(x))\).

`CoordinateMap.IdempotentCoordinates.ofTangentRetraction` takes a linear inclusion and projection presenting the tangent image. It inverts the pointed change of coordinates and applies it to the linear inclusion and projection. The resulting maps satisfy the actual formal retraction equations, with composite \(e\) on the ambient coordinates. This step requires a presentation of the tangent image by a finite free module.
