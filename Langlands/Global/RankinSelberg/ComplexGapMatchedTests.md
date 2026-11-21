# Matching the split tests in the two Godement integrals

`complexGapMatchedTests` integrates the transformed dual test over its complementary rectangular rows. At retained determinant of absolute value one the result uses the positive square Fourier transform of the leading restriction. `alternateBlockTailKernel_reverse` identifies the common tail factor on the Weyl-translated ordinary side.

The proof applies the full split Fourier identity and then inverts the transform in the last column with the opposite character. The dual chart gives the original first tail column as the last frequency and reverses the other tail columns of the inverse transpose. Reindexing their product matches the tail factor in the ordinary formula. The measure-preserving complementary shear and the leading Fourier identity give the integral of the leading test and its absolute convergence for each fixed set of retained variables. [Jacquet, *Archimedean Rankin–Selberg integrals*, Section 10.3, (10.7)–(10.10)](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf)

`tailFactor_reverse` presents the shared tail factor in the head, final frequency, and later Fourier coordinates of the ordinary chart.
