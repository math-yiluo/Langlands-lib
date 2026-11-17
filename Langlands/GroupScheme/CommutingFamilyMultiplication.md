# Multiplication of finite commuting families

Worker 632.

Internal construction for the component product argument in Conrad's
Proposition 6.4.4 and Remark 6.4.5. This module works over any scheme, including
an empty base and an empty finite family. It constructs the actual homomorphism
from a finite categorical product to a group scheme from prescribed
homomorphisms whose images pairwise commute on every relative test scheme.

On points the map is Mathlib's `MonoidHom.noncommPiCoprod`. Its restriction to
one coordinate is the prescribed homomorphism. Precomposition of points
commutes with this construction, as checked on the single-coordinate
generators of the product. Fully faithful group-valued Yoneda then supplies
the actual group-scheme homomorphism. The file proves the point formula,
compatibility with the actual factor inclusions and containment of each factor
image in its image. It makes no assertion that multiplication is surjective or
an isomorphism.
