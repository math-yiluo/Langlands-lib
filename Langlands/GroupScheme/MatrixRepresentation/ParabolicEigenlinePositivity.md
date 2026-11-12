# Positive weights of proper parabolic coordinate eigenlines

This internal derived result combines the actual orbit-weight bounds, the
opposite open cell, and actual rank-one reversing normalizers. It introduces no
external-source assertion.

`HasProperParabolicEigenline rho iP j` means that the supplied subgroup preserves
the j-th coordinate line and the entire ambient group does not preserve it.
The name does not assert that the supplied subgroup is parabolic or is the
exact line stabilizer. The positivity theorems separately require it to
represent the actual dynamic parabolic of the specified cocharacter. No
irreducibility or faithfulness of the representation is assumed.

First, coordinate-line preservation for a representation of a reduced group
can be detected after one dominant morphism into that group. Each off-diagonal
entry in the selected universal column is a morphism to affine line.
Separated-target extensionality extends its vanishing from the dominant test
to the reduced group; naturality gives vanishing on every scheme test.
Invertibility then gives the global unit scalar required for line preservation.

For a smooth connected affine group, the actual product of the opposite
dynamic unipotent and the dynamic parabolic is a nonempty open subscheme of
the geometrically integral group and hence is dense. If both factors preserve
the coordinate line, their product does so, and the preceding dominant-test
criterion proves that the entire group preserves the line.

Suppose the cocharacter is diagonal in the representation and an actual
rational point conjugates it to its inverse. A parabolic eigenline has the
all-test orbit upper bound; the reversing point supplies the lower bound and
nonnegativity of its original integer weight. If that weight were zero, the
lower bound would kill every negative-weight coordinate of the opposite
unipotent's selected column. All remaining entries of that column equal the
identity entries by the opposite-unipotent matrix description. Thus this
unipotent also preserves the line. The dense opposite cell would make the
entire group preserve it, contrary to the stated proper-eigenline assumption.
The integer weight is therefore strictly positive.

The final theorem applies the actual rank-one normalizer construction to the
integral Weyl correction `normKernelCocharacter i nu`. Its hypotheses are a
connected reductive group over any field, an actual maximal split torus, a
generic cocharacter whose actual simple-relative-root set is a singleton,
represented dynamic subgroups for that corrected direction, a finite matrix
representation in which this direction is diagonal, and the proper-eigenline
condition. The ambient group may be nonsplit. The supplied diagonal integer
weight of the selected line is strictly positive.

This proves a geometric positivity input. It does not construct the required
adapted representation or diagonal basis, compare its weight to the chosen
height character, establish height estimates, or prove adelic chamber
coverage.
