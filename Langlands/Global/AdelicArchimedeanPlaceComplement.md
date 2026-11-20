# Removing one archimedean coordinate of an adelic matrix

`AdelicGL.assemblePlaces` assembles an adelic matrix from matrices at each real and complex place and an invertible matrix over the finite adeles. It uses `placeGL`, the mixed archimedean coordinate equivalence and the infinite–finite split.

At any chosen real or complex place \(v\), an adelic matrix \(x\) is \(y\iota_v(g)\), where \(g\) is its matrix at \(v\) and \(y\) is obtained by setting that matrix to the identity. The other coordinates of \(\iota_v(g)\) are the identity. Thus \(y\) commutes with the entire image of the place group. Both statements include the finite factor in \(y\).

This is an internal coordinate calculation for Task 7041. It lets the family of local section slices through commuting base points test every adelic point.
