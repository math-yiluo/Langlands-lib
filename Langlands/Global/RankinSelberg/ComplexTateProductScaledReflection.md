# Product Tate reflection for a scaled complex trace character

`ComplexTateProductScaledReflectionStatement` gives the entire normalized product Tate identity with Jacquet's negative trace kernel at a nonzero complex character parameter `a`. Every entry is integrated with the Library's self-dual measure. The reflected factor for each angular weight is the Library epsilon factor for character parameter `−a` and Haar scale `‖a‖`.

The proof compares the trace kernel and measure with the positive standard transform, then changes variables in the additive Tate integral by complex multiplication. The real determinant on a complex coordinate is the square of the complex modulus. Together with the radial and angular weights, the product Jacobian gives the dilation factor. The normalized dilation identity extends off the convergence chamber by the identity theorem along an affine line. Combining it with the entire standard reflection gives the stated epsilon product.

This implements the scaled diagonal Tate step of the matrix-coefficient functional equation in Jacquet, *Archimedean Rankin–Selberg Integrals* (2009), §4.7, equation (4.3).
