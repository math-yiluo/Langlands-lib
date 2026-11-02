# Laurent-valued kernel points for the unitary rank bound

Worker 37. This internal elementary lemma supports the split-rank upper bound.
For a finite type with at least two elements and one integral weight vector `a`,
it constructs a nonzero integral vector orthogonal to `a` under the finite sum
pairing. Choose distinct coordinates `i,j`. If `a i = 0`, the `i`-th coordinate
vector works. Otherwise use `a j` at coordinate `i` and `-a i` at coordinate `j`;
the `j`-th entry is nonzero and the dot product vanishes by commutativity.
This is a derived integer calculation, independent of any characteristic or
field hypothesis. The actual upper-bound argument using this vector is separate.

The Laurent-specialization helpers evaluate a monomial of weight `a` at
coordinates `t^(m i)`, obtaining `C r * T(∑ i, a i * m i)`. A finite-product
induction proves the power identity. Distinct Laurent powers are distinct units
over a nonzero ring, by equality of coefficients. Consequently the actual
split-torus point `laurentPowerPoint R I m` is nonidentity whenever `m ≠ 0`.
These helpers use the existing affine-point equivalence and do not assume a
representation is faithful or has a particular support.
