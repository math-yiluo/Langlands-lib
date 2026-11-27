# Actual binary tensor classes in the matrix Levi

Let \(F\) be a nonarchimedean local field with data `T`. For positive
ranks \(a,b\), `localFieldBinaryLeviTensorFunctor` forms the external
tensor of two smooth complex representations on
\(\mathrm{GL}_a(F)\times\mathrm{GL}_b(F)\). Admissibility of the
finite-length factors and factorwise composition series give finite length
of that tensor.
The tensor carrier comparison with the ordinary binary tensor product
gives exactness separately in each variable.

`localFieldBinaryLeviTensorMap` takes the tensor product of the two exact
Grothendieck groups to the exact group of the product Levi. Evaluating a
pure tensor of object classes yields the class of the actual external
tensor. `localFieldBinaryLeviTensorMap_induced` takes
`hm : LocalFieldMatrixParabolicExactLength T (a + b)` and
`hx : LocalFieldBinaryProductExactLengthStatement`. It uses the induction
length and short-exact-sequence clauses of `hm` at the binary shape to
form the ambient induction map. The witness `hx` gives finite length and
separate exactness for the homogeneous product. On each pair of object
classes, the component of `binaryNormalizedProductPositiveIso` supplies the
actual induced equivalence. Bilinear class generation extends this equality
to all exact classes.

Zelevinsky's construction of the graded multiplication in §1.7 first
uses external tensor classes on the product Levi and then induces to
the larger group. The maps here implement those two operations on the
exact Grothendieck groups of actual representations.

- `zelevinsky-1980-induced-ii`, SHA-256
  `663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`,
  §1.7, printed pp. 172–173.
