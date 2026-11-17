# Continuous simple-root functions on adelic GL

This internal construction extends continuous functions of the simple-root
row to the actual adelic general linear group. The function must have the
coordinate symmetries supplied by the Schwartz majorant construction.

The proof applies the closed quotient-map descent from `CompactFactorDescent`
to multiplication of the upper triangular subgroup by the standard compact
subgroup. Surjectivity is the published adelic Iwasawa decomposition.
If two upper triangular factors represent the same fiber, their quotient lies
in the triangular compact intersection. `TriangularSchwartzCompatibility`
therefore identifies their simple-root function values.

The extension is continuous by descent. Multiplication on the left by an upper
unipotent matrix does not change the upper triangular diagonal. Multiplication
on the right by a standard compact element can be absorbed in the compact
factor. These give the two stated invariances on the actual matrix group.
