# Complementary Fourier marginals

`integral_complexBlockFourier_complement` uses three finite complex coordinate
blocks. In frequency variables it fixes the first block, sets the second
to zero and integrates out the third. The result is the Fourier transform
on the first block of the original test restricted to zero in the third
block and integrated over the second.

The proof fixes the frequency in the first block and integrates over the
first two input blocks with the corresponding unitary trace character.
This is a weighted Schwartz marginal in the remaining input block. Fubini
identifies its Fourier transform with the original three-block transform
at zero second frequency. Inversion at zero then gives the stated
restriction in the third input block. A second use of Fubini leaves the
first-block Fourier integral.

For a square matrix the three blocks are the diagonal, the strict upper
entries and the strict lower entries.
