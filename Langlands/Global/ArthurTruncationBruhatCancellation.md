# Cancellation in each Weyl cell

Swap the finite parabolic and Weyl sums, using the minimum-length criterion. At a fixed left-minimal Weyl element, the allowed right indices are all subsets of the positive simple roots. Their intersection with the simple images from the testing Levi is the neutral subset. Holding that intersection fixed determines both smaller parabolics, the outer rational coset type, the radical quotient and its measure.

For each fixed intersection, the finite source sum can therefore pass inside the summable outer coset sum and the integrable fiber terms. At a common integration point the cutoff is the only factor varying with the source index. Expanding the transported fundamental weight in the full weights gives nonnegative coefficients on the free roots, zero coefficients on the neutral roots and nonpositive coefficients outside the allowed set. Strict positivity of its value is the hypothesis of `alternatingCutoff_eq_zero`. The payload includes the condition of belonging to the fixed intersection, so cancellation holds within each fiber.

This implements the alternating-sum argument of Arthur (1980), Lemma 1.1, pp. 90–91, with the common integrals supplied by the geometric-lemma computation of Bernstein–Lapid (2024), §6.10.
