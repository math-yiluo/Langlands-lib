# Actual intertwiners detected by character spaces

This internal derived module supplies the linear algebra for classifying
simple representations from their actual characters. An actual
intertwiner preserves every character space. Conversely, if the source
character spaces span, a matrix preserving all character spaces is an
actual intertwiner on every affine algebra test. To prove the converse,
apply an arbitrary original-field coefficient functional to a test
matrix: that coefficient endomorphism acts by a scalar on every
character space. The commutation defect therefore vanishes on the
spanning family and hence everywhere.

If two representations have a common nonzero character space and the
source character spaces span, there is a nonzero actual intertwiner.
Project onto the common source character space, take a linear
functional nonzero on a chosen vector, and multiply its value by a
chosen nonzero target character vector. The resulting linear map
preserves all character spaces and is nonzero on the chosen vector.

A nonzero actual intertwiner between irreducible representations is
bijective: its stable kernel and image are forced by irreducibility to
be zero and the whole target respectively. A nonzero intertwiner over
any extension field also has a nonzero original-field intertwiner
coefficient. Choose a nonzero matrix entry, choose a linear functional
on the extension field taking this entry to one, and descend the
intertwiner entrywise. These lemmas make no smoothness or reducedness
assumption and use all affine algebra tests throughout.
