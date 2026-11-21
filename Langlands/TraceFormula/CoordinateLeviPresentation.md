# Coordinate Levi subgroups in the discrete trace sum

`CoordinateLevi.Presentation` orders the blocks of an actual partition of
`Fin n`. Its permutation carries each consecutive block of the Library's
`GeneralLinear.BlockShape` onto that block of the partition. The three
subgroup schemes are the Library's concrete block schemes, using the
resulting weights in the original coordinates. Each regular block
permutation has a rational permutation-matrix representative. In the chosen
numbering it sends the `j`th coordinate in a block to the `j`th coordinate
in its image block.

`CoordinateLeviPresentationStatement` asserts existence and the three
standard-coordinate comparisons over commutative rings, along with the
action of each representative on the actual blocks. The outer sum counts
each partition once, independently of its chosen presentation.

This is the general linear group coordinate interpretation of the groups
containing the fixed minimal Levi in Arthur–Clozel (1989), II.1,
printed pp. 75–78, and the Levi and Weyl indices of (9.2) and (4.1)–(4.2),
printed pp. 132 and 203. Registered source `arthur-clozel-1989-base-change`,
SHA-256 `c2e47ee562810367ebcacd3f1c242eda40b9e78b271668e36d99ce31001f9a19`.
