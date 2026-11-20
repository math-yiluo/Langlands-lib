# Common-strip reflection for the full diagonal complex Fourier transform

`ComplexTateProductFullFourierStatement` gives a simultaneous reflection of the normalized product Tate integral. Its Fourier transform uses the positive complex trace character with self-dual measure twice Euclidean area in each coordinate. On the region where every inducing parameter has real part strictly between zero and one, the transform reflects each parameter to `1 − u`, negates each angular weight, and multiplies the original normalized integral by the product of the scalar phases `I ^ |m|`.

The proof applies the scalar common-strip reflection successively over a finite set of coordinates. It identifies successive partial transforms with the corresponding product integral, using a point mass at each coordinate held fixed. Schwartz decay gives integrability for these mixed product measures, so Fubini accounts for one added coordinate at a time. On the full set of coordinates, the product of scalar characters is the trace character of the sum of the coordinate products.

This derives the product Tate step of the matrix-coefficient functional equation in Jacquet, *Archimedean Rankin–Selberg Integrals* (2009), §4.7, equation (4.3), from the common-strip scalar identity.
