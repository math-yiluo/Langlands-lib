# Meromorphic product Tate equation

`complexDiagonalTateEquation` gives the normalized product equation as an equality of punctured germs in the common spectral variable. The only premise is the scalar `ComplexArchimedeanTateStatement`, used through its Gaussian normalization.

The proof first enlarges the common product strip one coordinate at a time. On each coordinate line, the identity theorem for meromorphic functions gives the equality of germs. At points where the possible radial Mellin denominators are nonzero, both sides are continuous and the equality also holds at the center of the germs. This gives the equality for independent parameters away from the possible poles in each coordinate.

The proof then restricts the parameters to \(u_i=s+t_i\). Near a point with sufficiently large imaginary part all the coordinate exponents and their reflections avoid the possible Mellin poles, so the two sides agree there. A second use of the meromorphic identity theorem gives the equality of punctured germs on the whole line.
